||| Graded Monad for Obligation Tracking
|||
||| This module provides type-level tracking of computational obligations:
||| - Resource consumption (cycles, memory)
||| - External calls (inter-canister, HTTP)
||| - State modifications
||| - Acquired resources that need release
|||
||| Based on the Karma Monad paper: "obligations persist and accumulate"
|||
||| Key principle: Composability = existence of recovery-preserving morphisms
||| where obligations are explicit in the type signature.
|||
||| Usage:
|||   -- Type signature shows obligations
|||   process : GFR [CyclesConsumed 1000, ExternalCall "ledger"] Result
|||   process = gdo
|||     gconsumeCycles 1000
|||     gcall "ledger"
|||     gpure result
module Karma.Graded

import public FRC.Conflict
import public FRC.Evidence
import public ICP.Types
import Data.List

%default total

-- =============================================================================
-- Obligation Types
-- =============================================================================

||| Obligations that computations can incur
||| These are tracked at the type level during composition
public export
data Obligation : Type where
  ||| Cycles consumed by computation
  CyclesConsumed : (amount : Nat) -> Obligation

  ||| External inter-canister call made
  ExternalCall : (target : String) -> Obligation

  ||| HTTP outcall made
  HttpCall : (url : String) -> Obligation

  ||| State was modified (non-query operation)
  StateModified : Obligation

  ||| Resource acquired that may need cleanup
  ResourceHeld : (resource : String) -> Obligation

  ||| Permission required for operation
  PermissionRequired : (permission : String) -> Obligation

  ||| Async operation pending
  AsyncPending : (callId : Nat) -> Obligation

public export
Show Obligation where
  show (CyclesConsumed n) = "CyclesConsumed(" ++ show n ++ ")"
  show (ExternalCall t) = "ExternalCall(" ++ t ++ ")"
  show (HttpCall u) = "HttpCall(" ++ u ++ ")"
  show StateModified = "StateModified"
  show (ResourceHeld r) = "ResourceHeld(" ++ r ++ ")"
  show (PermissionRequired p) = "PermissionRequired(" ++ p ++ ")"
  show (AsyncPending c) = "AsyncPending(" ++ show c ++ ")"

public export
Eq Obligation where
  CyclesConsumed n1 == CyclesConsumed n2 = n1 == n2
  ExternalCall t1 == ExternalCall t2 = t1 == t2
  HttpCall u1 == HttpCall u2 = u1 == u2
  StateModified == StateModified = True
  ResourceHeld r1 == ResourceHeld r2 = r1 == r2
  PermissionRequired p1 == PermissionRequired p2 = p1 == p2
  AsyncPending c1 == AsyncPending c2 = c1 == c2
  _ == _ = False

-- =============================================================================
-- Obligation List Operations (Type-level)
-- =============================================================================

||| Type alias for obligation lists
public export
Obligations : Type
Obligations = List Obligation

||| Empty obligation list
public export
noObligations : Obligations
noObligations = []

||| Combine obligation lists (used in bind)
public export
combineObs : Obligations -> Obligations -> Obligations
combineObs = (++)

-- =============================================================================
-- GFR: Graded Failure-Recovery Monad
-- =============================================================================

||| Graded Failure-Recovery monad
||| GFR obs a represents a computation that:
|||   - Incurs obligations listed in obs
|||   - Produces a value of type a (or fails with IcpFail)
|||   - Carries evidence regardless of success/failure
|||
||| The grading (obs) is a type-level list that accumulates through bind,
||| making all side effects visible in the type signature.
public export
data GFR : (obligations : Obligations) -> (result : Type) -> Type where
  ||| Pure value with no obligations
  GPure : (value : a) -> (evidence : Evidence) -> GFR [] a

  ||| Failure with no additional obligations
  GFail : (failure : IcpFail) -> (evidence : Evidence) -> GFR [] a

  ||| Sequential composition accumulating obligations
  GBind : GFR obs1 a -> (a -> GFR obs2 b) -> GFR (obs1 ++ obs2) b

  ||| Consume cycles
  GConsumeCycles : (amount : Nat) -> Evidence -> GFR [CyclesConsumed amount] ()

  ||| Make external call
  GExternalCall : (target : String) -> Evidence -> GFR [ExternalCall target] ()

  ||| Make HTTP outcall
  GHttpCall : (url : String) -> Evidence -> GFR [HttpCall url] ()

  ||| Modify state
  GModifyState : Evidence -> GFR [StateModified] ()

  ||| Acquire resource
  GAcquireResource : (resource : String) -> Evidence -> GFR [ResourceHeld resource] ()

  ||| Require permission
  GRequirePermission : (permission : String) -> Evidence -> GFR [PermissionRequired permission] ()

  ||| Start async operation
  GStartAsync : (callId : Nat) -> Evidence -> GFR [AsyncPending callId] ()

-- =============================================================================
-- Show instance
-- =============================================================================

public export
Show a => Show (GFR obs a) where
  show (GPure v e) = "GPure(" ++ show v ++ ")"
  show (GFail f e) = "GFail(" ++ show f ++ ")"
  show (GBind x f) = "GBind(...)"
  show (GConsumeCycles n e) = "GConsumeCycles(" ++ show n ++ ")"
  show (GExternalCall t e) = "GExternalCall(" ++ t ++ ")"
  show (GHttpCall u e) = "GHttpCall(" ++ u ++ ")"
  show (GModifyState e) = "GModifyState"
  show (GAcquireResource r e) = "GAcquireResource(" ++ r ++ ")"
  show (GRequirePermission p e) = "GRequirePermission(" ++ p ++ ")"
  show (GStartAsync c e) = "GStartAsync(" ++ show c ++ ")"

-- =============================================================================
-- Graded Functor
-- =============================================================================

||| Map over the result, preserving obligation grading
public export
gmap : (a -> b) -> GFR obs a -> GFR obs b
gmap f (GPure v e) = GPure (f v) e
gmap f (GFail x e) = GFail x e
gmap f (GBind m k) = GBind m (\a => gmap f (k a))
gmap f (GConsumeCycles n e) = GBind (GConsumeCycles n e) (\() => GPure (f ()) e)
gmap f (GExternalCall t e) = GBind (GExternalCall t e) (\() => GPure (f ()) e)
gmap f (GHttpCall u e) = GBind (GHttpCall u e) (\() => GPure (f ()) e)
gmap f (GModifyState e) = GBind (GModifyState e) (\() => GPure (f ()) e)
gmap f (GAcquireResource r e) = GBind (GAcquireResource r e) (\() => GPure (f ()) e)
gmap f (GRequirePermission p e) = GBind (GRequirePermission p e) (\() => GPure (f ()) e)
gmap f (GStartAsync c e) = GBind (GStartAsync c e) (\() => GPure (f ()) e)

-- =============================================================================
-- Graded Monad Operations
-- =============================================================================

||| Pure value with no obligations
public export
gpure : a -> GFR [] a
gpure v = GPure v emptyEvidence

||| Pure with evidence
public export
gpureWith : a -> Evidence -> GFR [] a
gpureWith = GPure

||| Failure with no obligations
public export
gfail : IcpFail -> GFR [] a
gfail f = GFail f emptyEvidence

||| Failure with evidence
public export
gfailWith : IcpFail -> Evidence -> GFR [] a
gfailWith = GFail

||| Sequential composition (bind) - obligations accumulate
public export
gbind : GFR obs1 a -> (a -> GFR obs2 b) -> GFR (obs1 ++ obs2) b
gbind = GBind

||| Sequential composition, discarding first result
public export
gthen : GFR obs1 () -> GFR obs2 b -> GFR (obs1 ++ obs2) b
gthen m1 m2 = GBind m1 (\() => m2)

-- =============================================================================
-- Obligation-Incurring Operations
-- =============================================================================

||| Record cycles consumption
public export
gconsumeCycles : (amount : Nat) -> GFR [CyclesConsumed amount] ()
gconsumeCycles n = GConsumeCycles n (mkEvidence Update "gconsumeCycles" ("Consumed " ++ show n ++ " cycles"))

||| Record external canister call
public export
gexternalCall : (target : String) -> GFR [ExternalCall target] ()
gexternalCall t = GExternalCall t (mkEvidence Update "gexternalCall" ("Called " ++ t))

||| Record HTTP outcall
public export
ghttpCall : (url : String) -> GFR [HttpCall url] ()
ghttpCall u = GHttpCall u (mkEvidence HttpRequest "ghttpCall" ("HTTP to " ++ u))

||| Record state modification
public export
gmodifyState : GFR [StateModified] ()
gmodifyState = GModifyState (mkEvidence Update "gmodifyState" "State modified")

||| Acquire a resource (creates obligation to release)
public export
gacquireResource : (resource : String) -> GFR [ResourceHeld resource] ()
gacquireResource r = GAcquireResource r (mkEvidence Update "gacquireResource" ("Acquired " ++ r))

||| Require a permission
public export
grequirePermission : (permission : String) -> GFR [PermissionRequired permission] ()
grequirePermission p = GRequirePermission p (mkEvidence Update "grequirePermission" ("Required " ++ p))

||| Start async operation
public export
gstartAsync : (callId : Nat) -> GFR [AsyncPending callId] ()
gstartAsync c = GStartAsync c (mkEvidence Update "gstartAsync" ("Started async " ++ show c))

-- =============================================================================
-- Pure Computations (no obligations)
-- =============================================================================

||| Perform a pure computation
public export
gcompute : a -> GFR [] a
gcompute = gpure

||| Guard that fails if condition is false
public export
gguard : Bool -> IcpFail -> GFR [] ()
gguard True  _ = gpure ()
gguard False f = gfail f

||| Require Maybe to be Just
public export
grequireJust : Maybe a -> IcpFail -> GFR [] a
grequireJust (Just v) _ = gpure v
grequireJust Nothing  f = gfail f

||| Require Either to be Right
public export
grequireRight : Either String a -> (String -> IcpFail) -> GFR [] a
grequireRight (Right v) _ = gpure v
grequireRight (Left e) f  = gfail (f e)

-- =============================================================================
-- Evidence manipulation
-- =============================================================================

||| Add tag to evidence in GFR
public export
gtag : String -> GFR obs a -> GFR obs a
gtag t (GPure v e) = GPure v (addTag t e)
gtag t (GFail f e) = GFail f (addTag t e)
gtag t (GBind m k) = GBind m (\a => gtag t (k a))
gtag t (GConsumeCycles n e) = GConsumeCycles n (addTag t e)
gtag t (GExternalCall x e) = GExternalCall x (addTag t e)
gtag t (GHttpCall u e) = GHttpCall u (addTag t e)
gtag t (GModifyState e) = GModifyState (addTag t e)
gtag t (GAcquireResource r e) = GAcquireResource r (addTag t e)
gtag t (GRequirePermission p e) = GRequirePermission p (addTag t e)
gtag t (GStartAsync c e) = GStartAsync c (addTag t e)

-- =============================================================================
-- Obligation Queries (Type-level)
-- =============================================================================

||| Check if obligations include cycles consumption
public export
hasCyclesObligation : Obligations -> Bool
hasCyclesObligation [] = False
hasCyclesObligation (CyclesConsumed _ :: _) = True
hasCyclesObligation (_ :: xs) = hasCyclesObligation xs

||| Check if obligations include external calls
public export
hasExternalCallObligation : Obligations -> Bool
hasExternalCallObligation [] = False
hasExternalCallObligation (ExternalCall _ :: _) = True
hasExternalCallObligation (_ :: xs) = hasExternalCallObligation xs

||| Check if obligations include state modification
public export
hasStateModifiedObligation : Obligations -> Bool
hasStateModifiedObligation [] = False
hasStateModifiedObligation (StateModified :: _) = True
hasStateModifiedObligation (_ :: xs) = hasStateModifiedObligation xs

||| Sum total cycles consumed
public export
totalCyclesConsumed : Obligations -> Nat
totalCyclesConsumed [] = 0
totalCyclesConsumed (CyclesConsumed n :: xs) = n + totalCyclesConsumed xs
totalCyclesConsumed (_ :: xs) = totalCyclesConsumed xs

||| Count external calls
public export
countExternalCalls : Obligations -> Nat
countExternalCalls [] = 0
countExternalCalls (ExternalCall _ :: xs) = 1 + countExternalCalls xs
countExternalCalls (_ :: xs) = countExternalCalls xs

-- =============================================================================
-- Graded do-notation support
-- =============================================================================

||| Namespace for graded do-notation
||| Usage: GFR.do { x <- action1; y <- action2; gpure (x, y) }
namespace GFR
  public export
  (>>=) : GFR obs1 a -> (a -> GFR obs2 b) -> GFR (obs1 ++ obs2) b
  (>>=) = GBind

  public export
  (>>) : GFR obs1 () -> GFR obs2 b -> GFR (obs1 ++ obs2) b
  (>>) = gthen

  public export
  pure : a -> GFR [] a
  pure = gpure

-- =============================================================================
-- Result type for running GFR
-- =============================================================================

||| Result of running a GFR computation
public export
data GFRResult : Obligations -> Type -> Type where
  GROk : (value : a) -> (evidence : Evidence) -> (obligations : Obligations) -> GFRResult obs a
  GRFail : (failure : IcpFail) -> (evidence : Evidence) -> GFRResult obs a

public export
Show a => Show (GFRResult obs a) where
  show (GROk v e obs) = "GROk(" ++ show v ++ ", obligations=" ++ show obs ++ ")"
  show (GRFail f e) = "GRFail(" ++ show f ++ ")"

-- =============================================================================
-- Type-level obligation proofs
-- =============================================================================

-- The type system ensures:
--
-- 1. Obligation visibility: All side effects appear in the type signature
--    processData : GFR [StateModified, CyclesConsumed 5000] Result
--
-- 2. Obligation accumulation: Composed computations accumulate obligations
--    combined : GFR [StateModified, ExternalCall "ledger", CyclesConsumed 1000] ()
--    combined = GFR.do
--      gmodifyState           -- adds StateModified
--      gexternalCall "ledger" -- adds ExternalCall "ledger"
--      gconsumeCycles 1000    -- adds CyclesConsumed 1000
--
-- 3. Query safety: Can require no state modification at type level
--    pureQuery : GFR [] Result  -- guaranteed no side effects
--
-- 4. Resource tracking: Acquired resources visible in type
--    withLock : GFR [ResourceHeld "mutex"] Result
