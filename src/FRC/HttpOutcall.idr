||| HTTP Outcall Patterns for ICP Canisters
|||
||| ICP canisters can make HTTP outcalls to external services.
||| This module provides FR-aware patterns for safe HTTP communication.
|||
||| Key concerns:
||| - Request validation
||| - Response parsing
||| - Timeout handling
||| - Retry logic
||| - Cost estimation (HTTP outcalls are expensive)
module FRC.HttpOutcall

import FRC.Conflict
import FRC.Evidence
import FRC.Outcome
import FRC.Cycles
import Data.String
import Data.List
import Data.Maybe

%default total

-- String helper functions using lambda syntax to avoid parser issues
startsWith : String -> String -> Bool
startsWith = \p, s => substr 0 (length p) s == p

containsStr : String -> String -> Bool
containsStr = \needle, haystack =>
  let needleLen = length needle
      haystackLen = length haystack
  in go needleLen haystackLen haystack needle 0
  where
    go : Nat -> Nat -> String -> String -> Nat -> Bool
    go needleLen haystackLen haystack needle i =
      if i + needleLen > haystackLen
        then False
        else if substr i needleLen haystack == needle
          then True
          else assert_total $ go needleLen haystackLen haystack needle (S i)

-- =============================================================================
-- HTTP Method
-- =============================================================================

||| HTTP request methods supported by IC
public export
data HttpMethod
  = GET
  | POST
  | HEAD

public export
Show HttpMethod where
  show GET  = "GET"
  show POST = "POST"
  show HEAD = "HEAD"

public export
Eq HttpMethod where
  GET  == GET  = True
  POST == POST = True
  HEAD == HEAD = True
  _ == _ = False

-- =============================================================================
-- HTTP Request
-- =============================================================================

||| HTTP header
public export
record HttpHeader where
  constructor MkHttpHeader
  name  : String
  value : String

public export
Show HttpHeader where
  show h = h.name ++ ": " ++ h.value

||| HTTP request configuration
public export
record HttpRequest where
  constructor MkHttpRequest
  url               : String
  method            : HttpMethod
  headers           : List HttpHeader
  body              : Maybe String    -- Request body (for POST)
  maxResponseBytes  : Nat             -- Max response size
  transformContext  : Maybe String    -- Transform function context

public export
Show HttpRequest where
  show r = show r.method ++ " " ++ r.url

||| Create GET request
public export
mkGetRequest : String -> HttpRequest
mkGetRequest url = MkHttpRequest url GET [] Nothing 10000 Nothing

||| Create POST request
public export
mkPostRequest : String -> String -> HttpRequest
mkPostRequest url body = MkHttpRequest url POST [] (Just body) 10000 Nothing

||| Add header to request
public export
withHeader : String -> String -> HttpRequest -> HttpRequest
withHeader name value r = { headers := MkHttpHeader name value :: r.headers } r

||| Set max response bytes
public export
withMaxResponse : Nat -> HttpRequest -> HttpRequest
withMaxResponse n r = { maxResponseBytes := n } r

-- =============================================================================
-- HTTP Response
-- =============================================================================

||| HTTP response from outcall
public export
record HttpResponse where
  constructor MkHttpResponse
  status  : Nat               -- HTTP status code
  headers : List HttpHeader   -- Response headers
  body    : String            -- Response body

public export
Show HttpResponse where
  show r = "HTTP " ++ show r.status ++ " (" ++ show (length r.body) ++ " bytes)"

||| Check if response indicates success (2xx)
public export
isSuccess : HttpResponse -> Bool
isSuccess r = r.status >= 200 && r.status < 300

||| Check if response indicates client error (4xx)
public export
isClientError : HttpResponse -> Bool
isClientError r = r.status >= 400 && r.status < 500

||| Check if response indicates server error (5xx)
public export
isServerError : HttpResponse -> Bool
isServerError r = r.status >= 500 && r.status < 600

||| Check if response should be retried (5xx or specific codes)
public export
shouldRetry : HttpResponse -> Bool
shouldRetry r = isServerError r || r.status == 429  -- Too Many Requests

-- =============================================================================
-- FR-aware HTTP Operations
-- =============================================================================

||| Validate HTTP request before sending
public export
validateRequest : HttpRequest -> FR ()
validateRequest req = do
  -- Check URL is not empty
  guard HttpRequest "url" (length req.url > 0) (ValidationError "URL cannot be empty")
  -- Check URL starts with https (IC requires HTTPS)
  guard HttpRequest "protocol" (startsWith "https://" req.url || startsWith "http://" req.url)
        (ValidationError "URL must start with http:// or https://")
  -- Check max response is reasonable
  guard HttpRequest "maxResponse" (req.maxResponseBytes > 0 && req.maxResponseBytes <= 2000000)
        (ValidationError "maxResponseBytes must be between 1 and 2MB")

||| Parse HTTP response
public export
parseResponse : HttpResponse -> FR HttpResponse
parseResponse resp =
  if isSuccess resp
    then Ok resp (mkEvidence HttpRequest "parseResponse" $ "HTTP " ++ show resp.status)
    else if isClientError resp
      then Fail (HttpError (cast resp.status) "Client error")
                (mkEvidence HttpRequest "parseResponse" $ "HTTP " ++ show resp.status)
      else if isServerError resp
        then Fail (HttpError (cast resp.status) "Server error")
                  (mkEvidence HttpRequest "parseResponse" $ "HTTP " ++ show resp.status)
        else Fail (HttpError (cast resp.status) "Unexpected status")
                  (mkEvidence HttpRequest "parseResponse" $ "HTTP " ++ show resp.status)

||| Handle HTTP response with custom success/failure handlers
public export
handleResponse : (HttpResponse -> FR a)       -- Success handler
              -> (Int -> String -> FR a)      -- Error handler
              -> HttpResponse
              -> FR a
handleResponse onSuccess onError resp =
  if isSuccess resp
    then onSuccess resp
    else onError (cast resp.status) resp.body

-- =============================================================================
-- Retry Logic
-- =============================================================================

||| Retry configuration
public export
record RetryConfig where
  constructor MkRetryConfig
  maxRetries    : Nat       -- Maximum retry attempts
  retryOn5xx    : Bool      -- Retry on server errors
  retryOn429    : Bool      -- Retry on rate limit
  baseDelayMs   : Nat       -- Base delay between retries

public export
Show RetryConfig where
  show c = "Retry(max=" ++ show c.maxRetries ++
           ", 5xx=" ++ show c.retryOn5xx ++
           ", 429=" ++ show c.retryOn429 ++ ")"

||| Default retry configuration
public export
defaultRetryConfig : RetryConfig
defaultRetryConfig = MkRetryConfig 3 True True 1000

||| No retry configuration
public export
noRetryConfig : RetryConfig
noRetryConfig = MkRetryConfig 0 False False 0

||| Check if should retry based on config and response
public export
shouldRetryWith : RetryConfig -> HttpResponse -> Bool
shouldRetryWith cfg resp =
  (cfg.retryOn5xx && isServerError resp) ||
  (cfg.retryOn429 && resp.status == 429)

||| Retry state
public export
record RetryState where
  constructor MkRetryState
  attempt      : Nat       -- Current attempt (0-indexed)
  lastStatus   : Nat       -- Last HTTP status
  totalCycles  : Nat       -- Total cycles consumed

||| Initial retry state
public export
initialRetryState : RetryState
initialRetryState = MkRetryState 0 0 0

||| Check if can retry
public export
canRetry : RetryConfig -> RetryState -> Bool
canRetry cfg state = state.attempt < cfg.maxRetries

-- =============================================================================
-- HTTP Outcall Cost Estimation
-- =============================================================================

||| Estimate cost for HTTP outcall
||| IC charges ~49T cycles base + request/response size fees
public export
estimateHttpCost : HttpRequest -> Nat
estimateHttpCost req =
  let baseCost = 49140000                            -- ~49T base
      requestSize = length req.url + maybe 0 length req.body
      requestCost = requestSize * 5200               -- ~5.2K per request byte
      responseCost = req.maxResponseBytes * 10400    -- ~10.4K per response byte
  in baseCost + requestCost + responseCost

||| Check if budget allows HTTP outcall
public export
checkHttpBudget : CyclesBudget -> HttpRequest -> FR ()
checkHttpBudget budget req =
  let cost = estimateHttpCost req
  in checkCycles HttpRequest "httpOutcall" budget cost

-- =============================================================================
-- Response Parsing Helpers
-- =============================================================================

||| Get header value by name
public export
getHeader : String -> HttpResponse -> Maybe String
getHeader name resp = map value (find (\h => h.name == name) resp.headers)

||| Check Content-Type header
public export
hasContentType : String -> HttpResponse -> Bool
hasContentType expected resp = case getHeader "Content-Type" resp of
  Just ct => containsStr expected ct
  Nothing => False

||| Require JSON content type
public export
requireJson : HttpResponse -> FR ()
requireJson resp =
  if hasContentType "application/json" resp
    then Ok () (mkEvidence HttpRequest "requireJson" "JSON response")
    else Fail (DecodeError "Expected JSON content type")
              (mkEvidence HttpRequest "requireJson" $
               "Got: " ++ Data.Maybe.fromMaybe "none" (getHeader "Content-Type" resp))

-- =============================================================================
-- HTTP Evidence Recording
-- =============================================================================

||| Record HTTP outcall in evidence
public export
recordHttpOutcall : HttpRequest -> HttpResponse -> Nat -> Nat -> Evidence -> Evidence
recordHttpOutcall req resp cyclesCost latencyMs e =
  recordHttp (MkHttpRecord req.url (show req.method) (cast resp.status) cyclesCost latencyMs) e

-- =============================================================================
-- Timeout Handling
-- =============================================================================

||| Timeout configuration
public export
record TimeoutConfig where
  constructor MkTimeoutConfig
  requestTimeoutMs : Nat     -- Per-request timeout
  totalTimeoutMs   : Nat     -- Total operation timeout

||| Default timeout (30 seconds)
public export
defaultTimeout : TimeoutConfig
defaultTimeout = MkTimeoutConfig 30000 60000

||| Check if timeout exceeded
public export
isTimedOut : TimeoutConfig -> Nat -> Bool
isTimedOut cfg elapsedMs = elapsedMs > cfg.totalTimeoutMs

||| Timeout failure
public export
timeoutError : String -> FR a
timeoutError url = Fail (Timeout $ "HTTP request to " ++ url ++ " timed out")
                        (mkEvidence HttpRequest "timeout" url)

-- =============================================================================
-- URL Building
-- =============================================================================

||| Build URL with query parameters
public export
buildUrl : String -> List (String, String) -> String
buildUrl base [] = base
buildUrl base params = base ++ "?" ++ joinParams params
  where
    encodeParam : (String, String) -> String
    encodeParam (k, v) = k ++ "=" ++ v  -- TODO: URL encode
    joinParams : List (String, String) -> String
    joinParams [] = ""
    joinParams [p] = encodeParam p
    joinParams (p :: ps) = encodeParam p ++ "&" ++ joinParams ps
