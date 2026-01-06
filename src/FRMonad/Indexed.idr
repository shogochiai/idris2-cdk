||| State-Indexed Failure-Recovery Monad
|||
||| Based on the FR Monad paper: "Recovery-Preserving Kleisli Semantics for World-Computer Virtual Machines"
|||
||| Section 7.1: State-Indexed FR Monad
|||   IFR : State → State → Type → Type
|||
||| Composition exists only if state transitions align.
||| This ensures that invalid state machine transitions are rejected at compile time.
module FRMonad.Indexed

import FRMonad.Failure
import FRMonad.Evidence

%default total

-- =============================================================================
-- State: Type-level state for tracking state machine transitions
-- =============================================================================

||| Type-level state markers for canister lifecycle
public export
data CanisterState : Type where
  Uninitialized : CanisterState
  Initialized   : CanisterState
  Running       : CanisterState
  Upgrading     : CanisterState
  Stopped       : CanisterState

-- =============================================================================
-- IFR: State-Indexed Failure-Recovery Monad
-- Section 7.1: IFR : State → State → Type → Type
-- =============================================================================

||| State-Indexed FR Monad
||| `pre` is the precondition state
||| `post` is the postcondition state
||| Composition is only valid when post of first matches pre of second
public export
data IFR : (pre : CanisterState) -> (post : CanisterState) -> Type -> Type where
  ||| Success: state transition from pre to post with value and evidence
  IOk   : (value : a) -> (evidence : Evidence) -> IFR pre post a
  ||| Failure: no state transition, stays at pre state
  IFail : (failure : Fail) -> (evidence : Evidence) -> IFR pre pre a

public export
Show a => Show (IFR pre post a) where
  show (IOk v e)   = "IOk(" ++ show v ++ ") " ++ show e
  show (IFail f e) = "IFail(" ++ show f ++ ") " ++ show e

-- =============================================================================
-- Basic accessors
-- =============================================================================

||| Check if result is success
public export
isIOk : IFR pre post a -> Bool
isIOk (IOk _ _)   = True
isIOk (IFail _ _) = False

||| Check if result is failure
public export
isIFail : IFR pre post a -> Bool
isIFail = not . isIOk

||| Extract evidence
public export
getIEvidence : IFR pre post a -> Evidence
getIEvidence (IOk _ e)   = e
getIEvidence (IFail _ e) = e

||| Extract failure if present
public export
getIFailure : IFR pre post a -> Maybe Fail
getIFailure (IOk _ _)   = Nothing
getIFailure (IFail f _) = Just f

-- =============================================================================
-- Indexed Functor
-- =============================================================================

||| Map over the value, preserving state indices
public export
imap : (a -> b) -> IFR pre post a -> IFR pre post b
imap f (IOk v e)   = IOk (f v) e
imap f (IFail x e) = IFail x e

-- =============================================================================
-- Indexed Monad operations
-- Section 7.1: Composition exists only if state transitions align
-- =============================================================================

||| Pure: No state change
public export
ipure : a -> IFR s s a
ipure v = IOk v emptyEvidence

||| Bind: State transitions must align (mid must match)
||| IFR pre mid a -> (a -> IFR mid post b) -> IFR pre post b
public export
ibind : IFR pre mid a -> (a -> IFR mid post b) -> IFR pre post b
ibind (IOk v e1) f = case f v of
  IOk v' e2   => IOk v' (combineEvidence e1 e2)
  IFail x e2  => IFail x (combineEvidence e1 e2)
ibind (IFail x e) _ = IFail x e

||| Sequence: Chain state transitions
public export
(>>>=) : IFR pre mid a -> (a -> IFR mid post b) -> IFR pre post b
(>>>=) = ibind

||| Ignore left result
public export
(>>>) : IFR pre mid () -> IFR mid post b -> IFR pre post b
(>>>) ma mb = ibind ma (\_ => mb)

-- =============================================================================
-- State transition constructors
-- =============================================================================

||| Initialize canister: Uninitialized → Initialized
public export
initialize : String -> a -> IFR Uninitialized Initialized a
initialize label value = IOk value (mkEvidence Init label "initialized")

||| Start canister: Initialized → Running
public export
start : String -> a -> IFR Initialized Running a
start label value = IOk value (mkEvidence Update label "started")

||| Begin upgrade: Running → Upgrading
public export
beginUpgrade : String -> a -> IFR Running Upgrading a
beginUpgrade label value = IOk value (mkEvidence PreUpgrade label "upgrade started")

||| Complete upgrade: Upgrading → Running
public export
completeUpgrade : String -> a -> IFR Upgrading Running a
completeUpgrade label value = IOk value (mkEvidence PostUpgrade label "upgrade completed")

||| Stop canister: Running → Stopped
public export
stop : String -> a -> IFR Running Stopped a
stop label value = IOk value (mkEvidence Update label "stopped")

||| Restart canister: Stopped → Running
public export
restart : String -> a -> IFR Stopped Running a
restart label value = IOk value (mkEvidence Update label "restarted")

-- =============================================================================
-- Operations within a state (no state change)
-- =============================================================================

||| Query operation (no state change)
public export
iquery : String -> a -> IFR Running Running a
iquery label value = IOk value (mkEvidence Query label "query")

||| Update operation (no state change, but mutates internal state)
public export
iupdate : String -> a -> IFR Running Running a
iupdate label value = IOk value (mkEvidence Update label "update")

||| Fail with no state change
public export
ifail : Phase -> String -> String -> Fail -> IFR s s a
ifail phase label detail failure = IFail failure (mkEvidence phase label detail)

-- =============================================================================
-- Recovery operations
-- =============================================================================

||| Handle failure, potentially recovering to same state
public export
ihandleWith : ((Fail, Evidence) -> IFR pre pre a) -> IFR pre post a -> IFR pre post a
ihandleWith _ (IOk v e)   = IOk v e
ihandleWith h (IFail f e) = h (f, e)

||| Try alternative on failure (both must have same state transition)
public export
iorElse : IFR pre post a -> Lazy (IFR pre post a) -> IFR pre post a
iorElse (IOk v e)   _   = IOk v e
iorElse (IFail _ _) alt = alt

-- =============================================================================
-- Boundary functions
-- =============================================================================

||| Run indexed FR and extract result
public export
runIFR : IFR pre post a -> Either (Fail, Evidence) (a, Evidence)
runIFR (IOk v e)   = Right (v, e)
runIFR (IFail f e) = Left (f, e)

||| Convert to non-indexed FR (loses state information)
public export
toFR : IFR pre post a -> (Evidence -> Evidence) -> Either (Fail, Evidence) (a, Evidence)
toFR (IOk v e) f   = Right (v, f e)
toFR (IFail x e) f = Left (x, f e)

-- =============================================================================
-- Example: Safe canister lifecycle
--
-- This type signature guarantees at compile time that:
-- 1. Canister starts uninitialized
-- 2. Must be initialized before running
-- 3. Must be running to serve queries/updates
-- 4. Upgrade follows proper pre/post sequence
--
-- lifecycle : IFR Uninitialized Running Config
-- lifecycle = initialize "setup" defaultConfig
--         >>> start "launch" ()
--
-- Invalid sequences like:
--   start "launch" () -- Error: Cannot start from Uninitialized
--   completeUpgrade "done" () -- Error: Cannot complete from Running
-- =============================================================================
