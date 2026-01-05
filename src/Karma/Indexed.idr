||| Indexed Monad for Call Lifecycle State Tracking
|||
||| This module provides type-level guarantees for ICP canister call handling:
||| - Reply can only be called once (Processing → Committed)
||| - Reject can only be called once (Processing → Reverted)
||| - No operations after terminal states (Committed/Reverted)
|||
||| Based on the Karma Monad paper: recovery-preserving morphisms with
||| state-indexed composition.
|||
||| Usage:
|||   program : IFR Init Committed ()
|||   program = do
|||     x <- icompute someValue    -- Init → Init
|||     ibegin                     -- Init → Processing
|||     result <- iprocess x       -- Processing → Processing
|||     ireply result              -- Processing → Committed (terminal)
module Karma.Indexed

import public FRC.Conflict
import public FRC.Evidence
import public ICP.Types
import Data.List

%default total

-- =============================================================================
-- Call State: Lifecycle states for ICP canister calls
-- =============================================================================

||| Call lifecycle states
||| These form a state machine with the following transitions:
|||   Init → Processing (via ibegin)
|||   Processing → Committed (via ireply)
|||   Processing → Reverted (via ireject/itrap)
|||   Committed/Reverted are terminal (no further transitions)
public export
data CallState : Type where
  Init       : CallState  -- Before call processing begins
  Processing : CallState  -- Actively processing, can reply/reject
  Committed  : CallState  -- Reply sent, terminal state
  Reverted   : CallState  -- Rejected/trapped, terminal state

public export
Show CallState where
  show Init       = "Init"
  show Processing = "Processing"
  show Committed  = "Committed"
  show Reverted   = "Reverted"

public export
Eq CallState where
  Init       == Init       = True
  Processing == Processing = True
  Committed  == Committed  = True
  Reverted   == Reverted   = True
  _ == _ = False

-- =============================================================================
-- IFR: Indexed Failure-Recovery Monad
-- =============================================================================

||| Indexed Failure-Recovery monad
||| IFR s t a represents a computation that:
|||   - Starts in state s
|||   - Ends in state t
|||   - Produces a value of type a (or fails with IcpFail)
|||   - Carries evidence regardless of success/failure
|||
||| The key insight: state transitions are tracked at the type level,
||| preventing invalid operation sequences at compile time.
public export
data IFR : (start : CallState) -> (end : CallState) -> (result : Type) -> Type where
  ||| Pure value, no state change
  IPure : (value : a) -> (evidence : Evidence) -> IFR s s a

  ||| Failure, no state change (failure doesn't change call state)
  IFail : (failure : IcpFail) -> (evidence : Evidence) -> IFR s s a

  ||| Sequential composition with state threading
  IBind : IFR s t a -> (a -> IFR t u b) -> IFR s u b

  ||| Begin processing (Init → Processing)
  IBegin : Evidence -> IFR Init Processing ()

  ||| Reply with value (Processing → Committed)
  ||| This is the ONLY way to reach Committed state
  IReply : (value : List Bits8) -> Evidence -> IFR Processing Committed ()

  ||| Reject with message (Processing → Reverted)
  IReject : (message : String) -> Evidence -> IFR Processing Reverted ()

  ||| Trap (abort) with message (Processing → Reverted)
  ITrap : (message : String) -> Evidence -> IFR Processing Reverted ()

-- =============================================================================
-- Show instance for debugging
-- =============================================================================

public export
Show a => Show (IFR s t a) where
  show (IPure v e) = "IPure(" ++ show v ++ ")"
  show (IFail f e) = "IFail(" ++ show f ++ ")"
  show (IBind x f) = "IBind(...)"
  show (IBegin e) = "IBegin"
  show (IReply v e) = "IReply(" ++ show (length v) ++ " bytes)"
  show (IReject m e) = "IReject(" ++ m ++ ")"
  show (ITrap m e) = "ITrap(" ++ m ++ ")"

-- =============================================================================
-- Indexed Functor
-- =============================================================================

||| Map over the result, preserving state indices
public export
imap : (a -> b) -> IFR s t a -> IFR s t b
imap f (IPure v e) = IPure (f v) e
imap f (IFail x e) = IFail x e
imap f (IBind m k) = IBind m (\a => imap f (k a))
imap f (IBegin e) = IBind (IBegin e) (\() => IPure (f ()) e)
imap f (IReply v e) = IBind (IReply v e) (\() => IPure (f ()) e)
imap f (IReject m e) = IBind (IReject m e) (\() => IPure (f ()) e)
imap f (ITrap m e) = IBind (ITrap m e) (\() => IPure (f ()) e)

-- =============================================================================
-- Indexed Monad Operations
-- =============================================================================

||| Pure value injection (no state change)
public export
ipure : a -> IFR s s a
ipure v = IPure v emptyEvidence

||| Pure with evidence
public export
ipureWith : a -> Evidence -> IFR s s a
ipureWith = IPure

||| Failure (no state change)
public export
ifail : IcpFail -> IFR s s a
ifail f = IFail f emptyEvidence

||| Failure with evidence
public export
ifailWith : IcpFail -> Evidence -> IFR s s a
ifailWith = IFail

||| Sequential composition (bind)
public export
ibind : IFR s t a -> (a -> IFR t u b) -> IFR s u b
ibind = IBind

||| Sequential composition, discarding first result
public export
ithen : IFR s t () -> IFR t u b -> IFR s u b
ithen m1 m2 = IBind m1 (\() => m2)

-- =============================================================================
-- State Transition Operations
-- =============================================================================

||| Begin processing (Init → Processing)
public export
ibegin : IFR Init Processing ()
ibegin = IBegin (mkEvidence Init "ibegin" "Starting call processing")

||| Begin with custom evidence
public export
ibeginWith : Evidence -> IFR Init Processing ()
ibeginWith = IBegin

||| Reply with raw bytes (Processing → Committed)
||| Type system ensures this can only be called once per call
public export
ireply : List Bits8 -> IFR Processing Committed ()
ireply bytes = IReply bytes (mkEvidence Update "ireply" "Sending reply")

||| Reply with evidence
public export
ireplyWith : List Bits8 -> Evidence -> IFR Processing Committed ()
ireplyWith = IReply

||| Reply empty (Processing → Committed)
public export
ireplyEmpty : IFR Processing Committed ()
ireplyEmpty = ireply []

||| Reject with message (Processing → Reverted)
public export
ireject : String -> IFR Processing Reverted ()
ireject msg = IReject msg (mkEvidence Update "ireject" msg)

||| Reject with evidence
public export
irejectWith : String -> Evidence -> IFR Processing Reverted ()
irejectWith = IReject

||| Trap (abort) with message (Processing → Reverted)
public export
itrap : String -> IFR Processing Reverted ()
itrap msg = ITrap msg (mkEvidence Update "itrap" msg)

||| Trap with evidence
public export
itrapWith : String -> Evidence -> IFR Processing Reverted ()
itrapWith = ITrap

-- =============================================================================
-- Computation within a state (no state change)
-- =============================================================================

||| Perform a pure computation, staying in the same state
public export
icompute : a -> IFR s s a
icompute = ipure

||| Guard that fails if condition is false (no state change)
public export
iguard : Bool -> IcpFail -> IFR s s ()
iguard True  _ = ipure ()
iguard False f = ifail f

||| Require Maybe to be Just (no state change)
public export
irequireJust : Maybe a -> IcpFail -> IFR s s a
irequireJust (Just v) _ = ipure v
irequireJust Nothing  f = ifail f

||| Require Either to be Right (no state change)
public export
irequireRight : Either String a -> (String -> IcpFail) -> IFR s s a
irequireRight (Right v) _ = ipure v
irequireRight (Left e) f  = ifail (f e)

-- =============================================================================
-- Evidence manipulation
-- =============================================================================

||| Add tag to evidence in IFR
public export
itag : String -> IFR s t a -> IFR s t a
itag t (IPure v e) = IPure v (addTag t e)
itag t (IFail f e) = IFail f (addTag t e)
itag t (IBind m k) = IBind m (\a => itag t (k a))
itag t (IBegin e) = IBegin (addTag t e)
itag t (IReply v e) = IReply v (addTag t e)
itag t (IReject m e) = IReject m (addTag t e)
itag t (ITrap m e) = ITrap m (addTag t e)

-- =============================================================================
-- Running/Interpreting IFR
-- =============================================================================

||| Result of running an IFR computation
public export
data IFRResult : CallState -> Type -> Type where
  ||| Successful completion with value
  IROk : (value : a) -> (evidence : Evidence) -> (finalState : CallState) -> IFRResult s a
  ||| Failed with error
  IRFail : (failure : IcpFail) -> (evidence : Evidence) -> (finalState : CallState) -> IFRResult s a
  ||| Committed (replied successfully)
  IRCommitted : (evidence : Evidence) -> IFRResult s ()
  ||| Reverted (rejected or trapped)
  IRReverted : (reason : String) -> (evidence : Evidence) -> IFRResult s ()

public export
Show a => Show (IFRResult s a) where
  show (IROk v e s) = "IROk(" ++ show v ++ ", " ++ show s ++ ")"
  show (IRFail f e s) = "IRFail(" ++ show f ++ ", " ++ show s ++ ")"
  show (IRCommitted e) = "IRCommitted"
  show (IRReverted r e) = "IRReverted(" ++ r ++ ")"

-- =============================================================================
-- Utility: Indexed do-notation support
-- =============================================================================

||| Namespace for indexed do-notation
||| Usage: IFR.do { x <- action1; y <- action2; ipure (x, y) }
namespace IFR
  public export
  (>>=) : IFR s t a -> (a -> IFR t u b) -> IFR s u b
  (>>=) = IBind

  public export
  (>>) : IFR s t () -> IFR t u b -> IFR s u b
  (>>) = ithen

  public export
  pure : a -> IFR s s a
  pure = ipure

-- =============================================================================
-- Example type signatures showing compile-time guarantees
-- =============================================================================

-- Example: A complete call handler
-- Note: The type signature guarantees Init → Committed transition
--
-- exampleHandler : IFR Init Committed ()
-- exampleHandler = IFR.do
--   ibegin                           -- Init → Processing
--   x <- icompute (1 + 1)            -- Processing → Processing
--   iguard (x == 2) (Internal "math broken")
--   ireply [0x00]                    -- Processing → Committed

-- =============================================================================
-- Type-level proofs (for documentation)
-- =============================================================================

-- Proof: Cannot reply twice
-- If we have `IFR Processing Committed ()` (ireply),
-- we cannot compose with another `ireply` because
-- `ireply : IFR Processing Committed ()` requires Processing,
-- but after first ireply we're in Committed.
-- This is enforced by the type system - no runtime check needed.

-- Proof: Cannot reject after commit
-- After `ireply`, state is Committed.
-- `ireject : IFR Processing Reverted ()` requires Processing.
-- Type mismatch prevents composition.

-- Proof: Cannot operate after terminal state
-- Both Committed and Reverted are terminal.
-- No IFR constructors produce transitions FROM these states
-- (except IPure/IFail which stay in same state).
