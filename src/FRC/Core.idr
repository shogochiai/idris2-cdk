||| Failure-Recovery Calculus Core Types for ICP
|||
||| This module re-exports all FRC submodules for convenient import.
||| Based on the FRC paper: "Failure-Recovery Calculus for World-Computer Virtual Machines"
|||
||| Key principles (Karma Monad):
||| - Classify failures instead of hiding them (no "Unknown" failures)
||| - Force observability (evidence always present)
||| - Localize blast radius (explicit boundaries)
||| - Require recovery procedures
|||
||| Module structure:
||| - FRC.Conflict   : Failure classification with severity and category
||| - FRC.Evidence   : Observable data for diagnosis and replay
||| - FRC.Outcome    : FR monad with recovery-aware combinators
||| - FRC.Cycles     : ICP cycles (resource) management
||| - FRC.Upgrade    : Canister upgrade and migration patterns
||| - FRC.HttpOutcall: HTTP outcall patterns
||| - FRC.EVMChain   : EVM blockchain interaction patterns
|||
||| Usage:
|||   import FRC.Core  -- Get everything
|||   -- or import specific modules:
|||   import FRC.Outcome
|||   import FRC.Conflict
module FRC.Core

-- Re-export core submodules
import public FRC.Conflict
import public FRC.Evidence
import public FRC.Outcome
import public FRC.Cycles
import public FRC.Upgrade

-- Note: FRC.HttpOutcall and FRC.EVMChain are NOT re-exported to avoid
-- type collisions. Import them explicitly when needed:
--   import FRC.HttpOutcall
--   import FRC.EVMChain

-- Re-export ICP.Types for convenience
import public ICP.Types

%default total

-- =============================================================================
-- Convenient type aliases
-- =============================================================================

||| Standard failure type (re-exported from Conflict)
-- IcpFail is already exported from FRC.Conflict

||| Standard evidence type (re-exported from Evidence)
-- Evidence is already exported from FRC.Evidence

||| Standard FR monad (re-exported from Outcome)
-- FR is already exported from FRC.Outcome

-- =============================================================================
-- Common patterns
-- =============================================================================

||| Run FR computation and convert to text response (for canister interface)
public export
runFRToText : Show a => FR a -> String
runFRToText (Ok v e)   = "OK: " ++ show v
runFRToText (Fail f e) = "ERROR: " ++ show f ++ "\n" ++ renderEvidence e

||| Run FR computation returning JSON-like response
public export
runFRToJson : Show a => FR a -> String
runFRToJson (Ok v e) =
  "{\"status\":\"ok\",\"value\":" ++ show v ++
  ",\"evidence\":{\"phase\":\"" ++ show e.phase ++ "\",\"label\":\"" ++ e.label ++ "\"}}"
runFRToJson (Fail f e) =
  "{\"status\":\"error\",\"error\":\"" ++ show f ++
  "\",\"severity\":\"" ++ show (severity f) ++
  "\",\"category\":\"" ++ show (category f) ++ "\"}"

-- =============================================================================
-- ICP-specific entry point helpers
-- =============================================================================

||| Wrap a query operation with proper evidence
public export
queryOp : String -> FR a -> FR a
queryOp label = inPhase Query . tag ("query:" ++ label)

||| Wrap an update operation with proper evidence
public export
updateOp : String -> FR a -> FR a
updateOp label = inPhase Update . tag ("update:" ++ label)

||| Wrap an init operation with proper evidence
public export
initOp : String -> FR a -> FR a
initOp label = inPhase Init . tag ("init:" ++ label)

-- =============================================================================
-- Error response encoding
-- =============================================================================

||| Convert IcpFail to reject code (for IC reject)
||| Maps failure categories to IC reject codes:
||| - 1: SYS_FATAL
||| - 2: SYS_TRANSIENT
||| - 3: DESTINATION_INVALID
||| - 4: CANISTER_REJECT
||| - 5: CANISTER_ERROR
public export
toRejectCode : IcpFail -> Int
toRejectCode f = case category f of
  SecurityConflict  => 4   -- CANISTER_REJECT
  StateConflict     => 5   -- CANISTER_ERROR
  ResourceConflict  => 2   -- SYS_TRANSIENT (might recover with more cycles)
  ExecutionConflict => 5   -- CANISTER_ERROR
  NetworkConflict   => 2   -- SYS_TRANSIENT (might recover)
  EncodingConflict  => 4   -- CANISTER_REJECT
  PolicyConflict    => 4   -- CANISTER_REJECT
  UpgradeConflict   => 1   -- SYS_FATAL

||| Convert FR failure to (code, message) for IC reject
public export
toReject : IcpFail -> (Int, String)
toReject f = (toRejectCode f, show f)

-- =============================================================================
-- Composable guards
-- =============================================================================

||| Require caller to be owner
public export
requireOwner : Phase -> String -> String -> String -> FR ()
requireOwner phase op expected actual = do
  guard phase op (expected == actual)
        (Unauthorized $ "Caller " ++ actual ++ " is not owner " ++ expected)
  tag "owner-check" (pure ())

||| Require valid proposal ID
public export
requireValidId : Phase -> String -> Nat -> Nat -> FR ()
requireValidId phase op id maxId = do
  guard phase op (id > 0 && id <= maxId)
        (NotFound $ "Invalid ID " ++ show id ++ " (max: " ++ show maxId ++ ")")
  tag "id-check" (pure ())

||| Require non-empty string
public export
requireNonEmpty : Phase -> String -> String -> String -> FR ()
requireNonEmpty phase op name value = do
  guard phase op (length value > 0)
        (ValidationError $ name ++ " cannot be empty")
  tag "non-empty-check" (pure ())

-- =============================================================================
-- Version info
-- =============================================================================

||| FRC module version
public export
frcVersion : Version
frcVersion = MkVersion 1 0 0
