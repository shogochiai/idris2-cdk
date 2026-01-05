||| EVM Blockchain Interaction Patterns for ICP Canisters
|||
||| ICP canisters can interact with external EVM blockchains via HTTP RPC.
||| This module provides FR-aware patterns for blockchain communication.
|||
||| Key concerns:
||| - Chain configuration
||| - Transaction lifecycle
||| - Block confirmation
||| - Reorg handling
||| - Gas estimation
module FRC.EVMChain

import FRC.Conflict
import FRC.Evidence
import FRC.Outcome
import FRC.HttpOutcall
import Data.List
import Data.Maybe

%default total

-- Helper to convert Nat to hex string (using Integer for div/mod)
showHex : Nat -> String
showHex n = go (cast {to=Integer} n) []
  where
    hexDigit : Integer -> Char
    hexDigit d = if d < 10 then chr (ord '0' + cast d) else chr (ord 'a' + cast d - 10)
    go : Integer -> List Char -> String
    go 0 [] = "0"
    go 0 acc = pack acc
    go k acc = assert_total $ go (k `div` 16) (hexDigit (k `mod` 16) :: acc)

-- =============================================================================
-- Chain Configuration
-- =============================================================================

||| Supported EVM blockchain networks
public export
data ChainType
  = Ethereum
  | Polygon
  | Arbitrum
  | Optimism
  | BSC
  | Avalanche
  | Base
  | Custom String    -- Custom chain ID

public export
Show ChainType where
  show Ethereum    = "Ethereum"
  show Polygon     = "Polygon"
  show Arbitrum    = "Arbitrum"
  show Optimism    = "Optimism"
  show BSC         = "BSC"
  show Avalanche   = "Avalanche"
  show Base        = "Base"
  show (Custom s)  = "Custom(" ++ s ++ ")"

public export
Eq ChainType where
  Ethereum   == Ethereum   = True
  Polygon    == Polygon    = True
  Arbitrum   == Arbitrum   = True
  Optimism   == Optimism   = True
  BSC        == BSC        = True
  Avalanche  == Avalanche  = True
  Base       == Base       = True
  Custom a   == Custom b   = a == b
  _ == _ = False

||| Get standard chain ID
public export
chainId : ChainType -> Nat
chainId Ethereum    = 1
chainId Polygon     = 137
chainId Arbitrum    = 42161
chainId Optimism    = 10
chainId BSC         = 56
chainId Avalanche   = 43114
chainId Base        = 8453
chainId (Custom _)  = 0  -- Custom chains need explicit ID

||| Chain configuration
public export
record ChainConfig where
  constructor MkChainConfig
  chainType        : ChainType
  rpcUrl           : String       -- HTTP RPC endpoint
  chainIdOverride  : Maybe Nat    -- Override chain ID
  blockTime        : Nat          -- Expected block time in seconds
  confirmations    : Nat          -- Required confirmations

public export
Show ChainConfig where
  show c = show c.chainType ++ " @ " ++ c.rpcUrl

||| Get effective chain ID
public export
effectiveChainId : ChainConfig -> Nat
effectiveChainId c = Data.Maybe.fromMaybe (chainId c.chainType) c.chainIdOverride

-- =============================================================================
-- Block and Transaction Types
-- =============================================================================

||| Block number (or special values)
public export
data BlockRef
  = BlockNumber Nat      -- Specific block number
  | Latest               -- Latest block
  | Pending              -- Pending block
  | Safe                 -- Safe block (finalized on PoS)
  | Finalized            -- Finalized block

public export
Show BlockRef where
  show (BlockNumber n) = "0x" ++ showHex n
  show Latest          = "latest"
  show Pending         = "pending"
  show Safe            = "safe"
  show Finalized       = "finalized"

||| Transaction hash (32 bytes as hex string)
public export
TxHash : Type
TxHash = String

||| Address (20 bytes as hex string with 0x prefix)
public export
Address : Type
Address = String

||| Transaction status
public export
data TxStatus
  = TxPending              -- Not yet included in block
  | TxIncluded Nat         -- Included in block N
  | TxConfirmed Nat Nat    -- Confirmed: block N with M confirmations
  | TxFinalized Nat        -- Finalized in block N
  | TxFailed String        -- Transaction failed with reason
  | TxDropped              -- Transaction dropped from mempool

public export
Show TxStatus where
  show TxPending           = "PENDING"
  show (TxIncluded b)      = "INCLUDED@" ++ show b
  show (TxConfirmed b c)   = "CONFIRMED@" ++ show b ++ "(" ++ show c ++ " confs)"
  show (TxFinalized b)     = "FINALIZED@" ++ show b
  show (TxFailed r)        = "FAILED: " ++ r
  show TxDropped           = "DROPPED"

||| Transaction receipt (simplified)
public export
record TxReceipt where
  constructor MkTxReceipt
  txHash           : TxHash
  blockNumber      : Nat
  gasUsed          : Nat
  success          : Bool
  logs             : Nat           -- Number of logs/events

public export
Show TxReceipt where
  show r = "Receipt(" ++ r.txHash ++ " @" ++ show r.blockNumber ++
           ", gas=" ++ show r.gasUsed ++
           (if r.success then " OK" else " FAILED") ++ ")"

-- =============================================================================
-- RPC Request/Response Types
-- =============================================================================

||| JSON-RPC request ID
public export
RpcId : Type
RpcId = Nat

||| JSON-RPC error
public export
record RpcError where
  constructor MkRpcError
  code    : Int
  message : String

public export
Show RpcError where
  show e = "RPC Error " ++ show e.code ++ ": " ++ e.message

||| JSON-RPC response (simplified)
public export
data RpcResponse a
  = RpcOk a
  | RpcErr RpcError

public export
Show a => Show (RpcResponse a) where
  show (RpcOk v)   = "RpcOk(" ++ show v ++ ")"
  show (RpcErr e)  = "RpcErr(" ++ show e ++ ")"

-- =============================================================================
-- FR-aware Chain Operations
-- =============================================================================

||| Validate chain configuration
public export
validateChainConfig : ChainConfig -> FR ()
validateChainConfig cfg = do
  -- Check RPC URL is not empty
  guard Update "rpcUrl" (length cfg.rpcUrl > 0)
        (ValidationError "RPC URL cannot be empty")
  -- Check confirmations is reasonable
  guard Update "confirmations" (cfg.confirmations <= 100)
        (ValidationError "Confirmations should be <= 100")
  -- Check block time is reasonable
  guard Update "blockTime" (cfg.blockTime > 0 && cfg.blockTime <= 600)
        (ValidationError "Block time should be 1-600 seconds")

||| Convert RPC response to FR
public export
fromRpcResponse : RpcResponse a -> Evidence -> FR a
fromRpcResponse (RpcOk v) e = Ok v e
fromRpcResponse (RpcErr err) e =
  Fail (CallError $ "RPC error " ++ show err.code ++ ": " ++ err.message) e

||| Check transaction status against minimum confirmations
public export
requireConfirmations : Nat -> TxStatus -> FR ()
requireConfirmations minConfs status = case status of
  TxPending => Fail (CallError "Transaction still pending")
                    (mkEvidence Update "requireConfirmations" "pending")
  TxIncluded b => Fail (CallError $ "Only included at block " ++ show b ++ ", need " ++ show minConfs ++ " confirmations")
                       (mkEvidence Update "requireConfirmations" "insufficient confirmations")
  TxConfirmed b confs =>
    if confs >= minConfs
      then Ok () (mkEvidence Update "requireConfirmations" $
                  show confs ++ " confirmations >= " ++ show minConfs)
      else Fail (CallError $ "Only " ++ show confs ++ " confirmations, need " ++ show minConfs)
                (mkEvidence Update "requireConfirmations" "insufficient confirmations")
  TxFinalized _ => Ok () (mkEvidence Update "requireConfirmations" "finalized")
  TxFailed r => Fail (CallError $ "Transaction failed: " ++ r)
                     (mkEvidence Update "requireConfirmations" "tx failed")
  TxDropped => Fail (CallError "Transaction dropped")
                    (mkEvidence Update "requireConfirmations" "tx dropped")

||| Check if transaction is in terminal state
public export
isTerminal : TxStatus -> Bool
isTerminal (TxFinalized _) = True
isTerminal (TxFailed _)    = True
isTerminal TxDropped       = True
isTerminal _               = False

-- =============================================================================
-- Gas Management
-- =============================================================================

||| Gas configuration
public export
record GasConfig where
  constructor MkGasConfig
  gasLimit    : Nat       -- Maximum gas to use
  maxFeePerGas : Nat      -- Max fee per gas (wei)
  maxPriorityFee : Nat    -- Max priority fee (wei)

public export
Show GasConfig where
  show g = "Gas(limit=" ++ show g.gasLimit ++
           ", maxFee=" ++ show g.maxFeePerGas ++
           ", priority=" ++ show g.maxPriorityFee ++ ")"

||| Default gas config for simple transfers
public export
defaultGasConfig : GasConfig
defaultGasConfig = MkGasConfig 21000 50000000000 1000000000  -- 21K gas, 50 gwei, 1 gwei priority

||| Validate gas configuration
public export
validateGasConfig : GasConfig -> FR ()
validateGasConfig cfg = do
  guard Update "gasLimit" (cfg.gasLimit > 0 && cfg.gasLimit <= 30000000)
        (ValidationError "Gas limit should be 1-30M")
  guard Update "maxFee" (cfg.maxFeePerGas > 0)
        (ValidationError "Max fee must be positive")
  guard Update "priority" (cfg.maxPriorityFee <= cfg.maxFeePerGas)
        (ValidationError "Priority fee cannot exceed max fee")

-- =============================================================================
-- Reorg Handling
-- =============================================================================

||| Reorg event
public export
record ReorgEvent where
  constructor MkReorgEvent
  oldHead   : Nat         -- Previous head block
  newHead   : Nat         -- New head block
  depth     : Nat         -- Reorg depth
  affected  : List TxHash -- Affected transactions

public export
Show ReorgEvent where
  show r = "Reorg(depth=" ++ show r.depth ++
           ", " ++ show r.oldHead ++ " -> " ++ show r.newHead ++
           ", " ++ show (length r.affected) ++ " txs affected)"

||| Check if transaction might be affected by reorg
public export
mightBeAffected : Nat -> Nat -> TxStatus -> Bool
mightBeAffected reorgDepth currentBlock status = case status of
  TxIncluded b   => minus currentBlock b < reorgDepth
  TxConfirmed b c => c < reorgDepth
  _              => False

-- =============================================================================
-- Chain Evidence Recording
-- =============================================================================

||| Record chain call in evidence
public export
recordChainCall : ChainConfig -> String -> Evidence -> Evidence
recordChainCall cfg method e =
  addTags ["chain:" ++ show cfg.chainType, "method:" ++ method] e

||| Record transaction submission
public export
recordTxSubmit : TxHash -> ChainConfig -> Evidence -> Evidence
recordTxSubmit txHash cfg e =
  addTags ["tx:" ++ txHash, "chain:" ++ show cfg.chainType] e

-- =============================================================================
-- Multi-chain Support
-- =============================================================================

||| Multi-chain operation context
public export
record MultiChainContext where
  constructor MkMultiChainContext
  chains : List ChainConfig
  primary : ChainType        -- Primary chain

||| Find chain config by type
public export
findChain : ChainType -> MultiChainContext -> Maybe ChainConfig
findChain t ctx = find (\c => c.chainType == t) ctx.chains

||| Require chain to be configured
public export
requireChain : ChainType -> MultiChainContext -> FR ChainConfig
requireChain chainType ctx = case findChain chainType ctx of
  Just cfg => Ok cfg (mkEvidence Update "requireChain" $ "Found " ++ show chainType)
  Nothing  => Fail (NotFound $ "Chain " ++ show chainType ++ " not configured")
                   (mkEvidence Update "requireChain" "chain not found")
