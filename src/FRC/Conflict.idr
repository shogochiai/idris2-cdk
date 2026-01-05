||| Failure Classification for ICP Canisters
|||
||| Following the Karma Monad principle: classify failures instead of hiding them.
||| Every failure has a severity (impact level) and category (failure domain).
||| This enables:
||| - Automated retry decisions based on severity
||| - Category-specific recovery strategies
||| - Proper observability and metrics
module FRC.Conflict

%default total

-- =============================================================================
-- Severity: Impact level of failure
-- =============================================================================

||| Severity indicates how serious a failure is and guides recovery strategy
||| - Critical: System-wide impact, immediate attention needed
||| - High: Significant impact, operation cannot proceed
||| - Medium: Localized impact, operation degraded
||| - Low: Minor impact, can continue with fallback
||| - Info: Not really a failure, informational only
public export
data Severity
  = Critical    -- System invariant violated, canister may be in bad state
  | High        -- Operation failed, cannot proceed
  | Medium      -- Operation degraded, partial success possible
  | Low         -- Minor issue, fallback available
  | Info        -- Informational, not a true failure

public export
Show Severity where
  show Critical = "CRITICAL"
  show High     = "HIGH"
  show Medium   = "MEDIUM"
  show Low      = "LOW"
  show Info     = "INFO"

public export
Eq Severity where
  Critical == Critical = True
  High     == High     = True
  Medium   == Medium   = True
  Low      == Low      = True
  Info     == Info     = True
  _ == _ = False

||| Severity ordering: Critical > High > Medium > Low > Info
public export
Ord Severity where
  compare Critical Critical = EQ
  compare Critical _        = GT
  compare High     Critical = LT
  compare High     High     = EQ
  compare High     _        = GT
  compare Medium   Critical = LT
  compare Medium   High     = LT
  compare Medium   Medium   = EQ
  compare Medium   _        = GT
  compare Low      Info     = GT
  compare Low      Low      = EQ
  compare Low      _        = LT
  compare Info     Info     = EQ
  compare Info     _        = LT

-- =============================================================================
-- Category: Domain classification of failure
-- =============================================================================

||| Category indicates the domain where failure occurred
||| This guides which recovery strategy to use
public export
data ConflictCategory
  = SecurityConflict    -- Auth/permission failures
  | StateConflict       -- State machine/consistency violations
  | ResourceConflict    -- Cycles/memory/storage limits
  | ExecutionConflict   -- Runtime/trap failures
  | NetworkConflict     -- Inter-canister/HTTP call failures
  | EncodingConflict    -- Candid/serialization failures
  | PolicyConflict      -- Business rule violations
  | UpgradeConflict     -- Upgrade/migration failures

public export
Show ConflictCategory where
  show SecurityConflict  = "SECURITY"
  show StateConflict     = "STATE"
  show ResourceConflict  = "RESOURCE"
  show ExecutionConflict = "EXECUTION"
  show NetworkConflict   = "NETWORK"
  show EncodingConflict  = "ENCODING"
  show PolicyConflict    = "POLICY"
  show UpgradeConflict   = "UPGRADE"

public export
Eq ConflictCategory where
  SecurityConflict  == SecurityConflict  = True
  StateConflict     == StateConflict     = True
  ResourceConflict  == ResourceConflict  = True
  ExecutionConflict == ExecutionConflict = True
  NetworkConflict   == NetworkConflict   = True
  EncodingConflict  == EncodingConflict  = True
  PolicyConflict    == PolicyConflict    = True
  UpgradeConflict   == UpgradeConflict   = True
  _ == _ = False

-- =============================================================================
-- IcpFail: Classified failure types for ICP
-- =============================================================================

||| ICP-specific failure classifications
||| These form a closed sum type - no "Unknown" failures allowed
||| Every constructor maps to a specific severity and category
public export
data IcpFail
  -- Execution conflicts (traps, runtime errors)
  = Trap String                         -- ic0.trap equivalent
  | SysInvariant String                 -- System invariant violation
  | Internal String                     -- Internal error (last resort)

  -- Network conflicts (inter-canister, HTTP)
  | Reject Int String                   -- Canister rejection (code, message)
  | CallError String                    -- Inter-canister call failure
  | Timeout String                      -- Operation timeout
  | HttpError Int String                -- HTTP outcall error (status, message)

  -- Encoding conflicts (Candid, serialization)
  | DecodeError String                  -- Candid/data decoding failure
  | EncodeError String                  -- Candid/data encoding failure

  -- State conflicts (consistency, concurrency)
  | StableMemError String               -- Stable memory operation failure
  | Conflict String                     -- Optimistic concurrency conflict
  | InvalidState String                 -- State machine violation
  | NotFound String                     -- Resource not found

  -- Security conflicts (auth, permissions)
  | Unauthorized String                 -- Permission/auth failure
  | PrincipalMismatch String            -- Expected vs actual principal

  -- Resource conflicts (cycles, memory, limits)
  | RateLimited String                  -- Rate/resource limit exceeded
  | InsufficientCycles Nat String       -- Need N cycles, message
  | MemoryExhausted String              -- Memory allocation failed

  -- Policy conflicts (business rules)
  | PolicyViolation String              -- Business rule violated
  | ValidationError String              -- Input validation failed

  -- Upgrade conflicts (migration, versioning)
  | UpgradeFailed String                -- Upgrade operation failed
  | VersionMismatch Nat Nat             -- Expected vs actual version
  | MigrationError String               -- State migration failed

public export
Show IcpFail where
  show (Trap s)                = "Trap: " ++ s
  show (SysInvariant s)        = "SysInvariant: " ++ s
  show (Internal s)            = "Internal: " ++ s
  show (Reject c m)            = "Reject(" ++ show c ++ "): " ++ m
  show (CallError s)           = "CallError: " ++ s
  show (Timeout s)             = "Timeout: " ++ s
  show (HttpError c m)         = "HttpError(" ++ show c ++ "): " ++ m
  show (DecodeError s)         = "DecodeError: " ++ s
  show (EncodeError s)         = "EncodeError: " ++ s
  show (StableMemError s)      = "StableMemError: " ++ s
  show (Conflict s)            = "Conflict: " ++ s
  show (InvalidState s)        = "InvalidState: " ++ s
  show (NotFound s)            = "NotFound: " ++ s
  show (Unauthorized s)        = "Unauthorized: " ++ s
  show (PrincipalMismatch s)   = "PrincipalMismatch: " ++ s
  show (RateLimited s)         = "RateLimited: " ++ s
  show (InsufficientCycles n s)= "InsufficientCycles(" ++ show n ++ "): " ++ s
  show (MemoryExhausted s)     = "MemoryExhausted: " ++ s
  show (PolicyViolation s)     = "PolicyViolation: " ++ s
  show (ValidationError s)     = "ValidationError: " ++ s
  show (UpgradeFailed s)       = "UpgradeFailed: " ++ s
  show (VersionMismatch e a)   = "VersionMismatch: expected " ++ show e ++ ", got " ++ show a
  show (MigrationError s)      = "MigrationError: " ++ s

-- =============================================================================
-- Classification functions
-- =============================================================================

||| Get severity of a failure
||| Critical: System invariants, stable memory, upgrade failures
||| High: Traps, auth failures, insufficient cycles
||| Medium: Call errors, timeouts, conflicts
||| Low: Not found, validation errors
public export
severity : IcpFail -> Severity
severity (Trap _)              = High
severity (SysInvariant _)      = Critical
severity (Internal _)          = High
severity (Reject _ _)          = Medium
severity (CallError _)         = Medium
severity (Timeout _)           = Medium
severity (HttpError _ _)       = Medium
severity (DecodeError _)       = Medium
severity (EncodeError _)       = Medium
severity (StableMemError _)    = Critical
severity (Conflict _)          = Medium
severity (InvalidState _)      = High
severity (NotFound _)          = Low
severity (Unauthorized _)      = High
severity (PrincipalMismatch _) = High
severity (RateLimited _)       = Medium
severity (InsufficientCycles _ _) = High
severity (MemoryExhausted _)   = Critical
severity (PolicyViolation _)   = Medium
severity (ValidationError _)   = Low
severity (UpgradeFailed _)     = Critical
severity (VersionMismatch _ _) = Critical
severity (MigrationError _)    = Critical

||| Get category of a failure
public export
category : IcpFail -> ConflictCategory
category (Trap _)              = ExecutionConflict
category (SysInvariant _)      = ExecutionConflict
category (Internal _)          = ExecutionConflict
category (Reject _ _)          = NetworkConflict
category (CallError _)         = NetworkConflict
category (Timeout _)           = NetworkConflict
category (HttpError _ _)       = NetworkConflict
category (DecodeError _)       = EncodingConflict
category (EncodeError _)       = EncodingConflict
category (StableMemError _)    = StateConflict
category (Conflict _)          = StateConflict
category (InvalidState _)      = StateConflict
category (NotFound _)          = StateConflict
category (Unauthorized _)      = SecurityConflict
category (PrincipalMismatch _) = SecurityConflict
category (RateLimited _)       = ResourceConflict
category (InsufficientCycles _ _) = ResourceConflict
category (MemoryExhausted _)   = ResourceConflict
category (PolicyViolation _)   = PolicyConflict
category (ValidationError _)   = PolicyConflict
category (UpgradeFailed _)     = UpgradeConflict
category (VersionMismatch _ _) = UpgradeConflict
category (MigrationError _)    = UpgradeConflict

-- =============================================================================
-- Recovery guidance
-- =============================================================================

||| Should this failure be retried?
||| Only Medium/Low severity + certain categories should retry
public export
isRetryable : IcpFail -> Bool
isRetryable f = case (severity f, category f) of
  (Medium, NetworkConflict)  => True   -- Network issues may be transient
  (Medium, StateConflict)    => True   -- Conflicts may resolve
  (Low, _)                   => True   -- Low severity can retry
  _                          => False  -- Critical/High or other categories

||| Can user recover from this failure?
||| User can fix: validation, policy violations, auth (re-authenticate)
public export
isUserRecoverable : IcpFail -> Bool
isUserRecoverable (ValidationError _)   = True
isUserRecoverable (PolicyViolation _)   = True
isUserRecoverable (Unauthorized _)      = True  -- User can re-authenticate
isUserRecoverable (NotFound _)          = True  -- User can provide valid ID
isUserRecoverable (InsufficientCycles _ _) = True  -- User can top up
isUserRecoverable _                     = False

||| Does this failure require developer attention?
public export
requiresDevAttention : IcpFail -> Bool
requiresDevAttention f = severity f >= High

-- =============================================================================
-- Predicate helpers for catchFail
-- =============================================================================

||| Match security-related failures
public export
isSecurityFail : IcpFail -> Bool
isSecurityFail f = category f == SecurityConflict

||| Match state-related failures
public export
isStateFail : IcpFail -> Bool
isStateFail f = category f == StateConflict

||| Match resource-related failures
public export
isResourceFail : IcpFail -> Bool
isResourceFail f = category f == ResourceConflict

||| Match network-related failures
public export
isNetworkFail : IcpFail -> Bool
isNetworkFail f = category f == NetworkConflict

||| Match encoding-related failures
public export
isEncodingFail : IcpFail -> Bool
isEncodingFail f = category f == EncodingConflict

||| Match upgrade-related failures
public export
isUpgradeFail : IcpFail -> Bool
isUpgradeFail f = category f == UpgradeConflict

||| Match critical failures
public export
isCriticalFail : IcpFail -> Bool
isCriticalFail f = severity f == Critical
