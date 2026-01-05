||| Cycles Resource Management for ICP Canisters
|||
||| ICP cycles are the fundamental resource for computation.
||| This module provides FR-aware cycles tracking and management.
|||
||| Key concerns:
||| - Developer cycles: canister operations cost cycles
||| - User cycles: users can attach cycles to calls
||| - Call cycles: inter-canister calls require cycles
||| - HTTP cycles: HTTP outcalls have cycle costs
module FRC.Cycles

import FRC.Conflict
import FRC.Evidence
import FRC.Outcome

%default total

-- =============================================================================
-- Cycles Budget: Resource limits
-- =============================================================================

||| Cycles budget for an operation
||| Tracks both limits and current consumption
public export
record CyclesBudget where
  constructor MkCyclesBudget
  available    : Nat         -- Cycles available
  limit        : Nat         -- Max cycles to spend
  consumed     : Nat         -- Cycles consumed so far
  reserved     : Nat         -- Cycles reserved for pending ops

public export
Show CyclesBudget where
  show b = "Budget(avail=" ++ show b.available ++
           ", limit=" ++ show b.limit ++
           ", used=" ++ show b.consumed ++
           ", reserved=" ++ show b.reserved ++ ")"

||| Create unlimited budget (for testing/simple cases)
public export
unlimitedBudget : Nat -> CyclesBudget
unlimitedBudget avail = MkCyclesBudget avail avail 0 0

||| Create limited budget
public export
limitedBudget : Nat -> Nat -> CyclesBudget
limitedBudget avail limit = MkCyclesBudget avail limit 0 0

||| Remaining cycles in budget
public export
remaining : CyclesBudget -> Nat
remaining b = minus b.limit (b.consumed + b.reserved)

||| Check if budget has sufficient cycles
public export
hasSufficient : CyclesBudget -> Nat -> Bool
hasSufficient b needed = remaining b >= needed

-- =============================================================================
-- Cycles operations
-- =============================================================================

||| Consume cycles from budget
public export
consumeCycles : Nat -> CyclesBudget -> Maybe CyclesBudget
consumeCycles amount b =
  if hasSufficient b amount
    then Just ({ consumed := b.consumed + amount } b)
    else Nothing

||| Reserve cycles for pending operation
public export
reserveCycles : Nat -> CyclesBudget -> Maybe CyclesBudget
reserveCycles amount b =
  if hasSufficient b amount
    then Just ({ reserved := b.reserved + amount } b)
    else Nothing

||| Release reserved cycles (operation completed or cancelled)
public export
releaseReserved : Nat -> CyclesBudget -> CyclesBudget
releaseReserved amount b = { reserved := minus b.reserved amount } b

||| Commit reserved cycles (operation succeeded, cycles spent)
public export
commitReserved : Nat -> CyclesBudget -> CyclesBudget
commitReserved amount b =
  { reserved := minus b.reserved amount
  , consumed := b.consumed + amount
  } b

-- =============================================================================
-- FR with Cycles tracking
-- =============================================================================

||| Require sufficient cycles or fail
public export
requireCycles : Phase -> String -> CyclesBudget -> Nat -> FR CyclesBudget
requireCycles phase label budget needed =
  case consumeCycles needed budget of
    Just newBudget => Ok newBudget (mkEvidence phase label $ "consumed " ++ show needed ++ " cycles")
    Nothing => Fail (InsufficientCycles needed $
                     "need " ++ show needed ++ " but only " ++ show (remaining budget) ++ " available")
                    (mkEvidence phase label "insufficient cycles")

||| Check cycles without consuming
public export
checkCycles : Phase -> String -> CyclesBudget -> Nat -> FR ()
checkCycles phase label budget needed =
  if hasSufficient budget needed
    then Ok () (mkEvidence phase label "cycles check passed")
    else Fail (InsufficientCycles needed $
               "need " ++ show needed ++ " but only " ++ show (remaining budget) ++ " available")
              (mkEvidence phase label "cycles check failed")

||| Reserve cycles for an async operation
public export
reserveForCall : Phase -> String -> CyclesBudget -> Nat -> FR CyclesBudget
reserveForCall phase label budget amount =
  case reserveCycles amount budget of
    Just newBudget => Ok newBudget (mkEvidence phase label $ "reserved " ++ show amount ++ " cycles")
    Nothing => Fail (InsufficientCycles amount "cannot reserve cycles")
                    (mkEvidence phase label "reservation failed")

-- =============================================================================
-- Cycles cost estimation
-- =============================================================================

||| Cost type for different operations
public export
data CyclesCost
  = FixedCost Nat                    -- Fixed cycle cost
  | PerByteCost Nat Nat              -- Base + per-byte cost
  | PerInstructionCost Nat Nat       -- Base + per-instruction estimate
  | HttpCost Nat Nat Nat             -- Base + request size + response size factors

public export
Show CyclesCost where
  show (FixedCost n) = "Fixed(" ++ show n ++ ")"
  show (PerByteCost base perByte) = "PerByte(" ++ show base ++ "+" ++ show perByte ++ "/byte)"
  show (PerInstructionCost base perInst) = "PerInst(" ++ show base ++ "+" ++ show perInst ++ "/inst)"
  show (HttpCost base reqFactor respFactor) = "Http(" ++ show base ++ ")"

||| Calculate cost for given size
public export
calculateCost : CyclesCost -> Nat -> Nat
calculateCost (FixedCost n) _ = n
calculateCost (PerByteCost base perByte) size = base + (perByte * size)
calculateCost (PerInstructionCost base perInst) instructions = base + (perInst * instructions)
calculateCost (HttpCost base reqFactor respFactor) size = base + (reqFactor * size) + (respFactor * size)

-- =============================================================================
-- ICP-specific cost constants (approximate)
-- =============================================================================

||| Approximate cost for inter-canister call
public export
interCanisterCallCost : CyclesCost
interCanisterCallCost = PerByteCost 590000 400  -- ~0.59T base + 400 per byte

||| Approximate cost for HTTP outcall
public export
httpOutcallCost : CyclesCost
httpOutcallCost = HttpCost 49140000 5200 10400  -- ~49T base

||| Cost for stable memory operations (per page = 64KB)
public export
stableMemoryGrowCost : CyclesCost
stableMemoryGrowCost = FixedCost 1000000  -- ~1M per page

||| Cost for instructions (per million)
public export
instructionCost : CyclesCost
instructionCost = PerInstructionCost 0 10  -- 10 cycles per instruction

-- =============================================================================
-- Budget-aware combinators
-- =============================================================================

||| Run operation within cycles budget
public export
withBudget : CyclesBudget -> (CyclesBudget -> FR (a, CyclesBudget)) -> FR a
withBudget budget f = do
  (result, _) <- f budget
  pure result

||| Track cycles consumed by operation
public export
trackCycles : Phase -> String -> Nat -> Nat -> FR a -> FR a
trackCycles phase label startCycles endCycles fr =
  withEvidence (\e => withCycles startCycles endCycles e) fr

||| Estimate and check cycles before operation
public export
estimateAndCheck : Phase -> String -> CyclesBudget -> CyclesCost -> Nat -> FR ()
estimateAndCheck phase label budget cost size =
  let needed = calculateCost cost size
  in checkCycles phase label budget needed

-- =============================================================================
-- Cycles accounting record
-- =============================================================================

||| Detailed cycles accounting for analysis
public export
record CyclesAccount where
  constructor MkCyclesAccount
  operationCycles : Nat        -- Cycles for computation
  callCycles      : Nat        -- Cycles sent in calls
  httpCycles      : Nat        -- Cycles for HTTP outcalls
  storageCycles   : Nat        -- Cycles for storage
  refundCycles    : Nat        -- Cycles refunded

public export
Show CyclesAccount where
  show a = "Account(op=" ++ show a.operationCycles ++
           ", calls=" ++ show a.callCycles ++
           ", http=" ++ show a.httpCycles ++
           ", storage=" ++ show a.storageCycles ++
           ", refund=" ++ show a.refundCycles ++ ")"

||| Empty cycles account
public export
emptyAccount : CyclesAccount
emptyAccount = MkCyclesAccount 0 0 0 0 0

||| Total cycles spent (excluding refunds)
public export
totalSpent : CyclesAccount -> Nat
totalSpent a = a.operationCycles + a.callCycles + a.httpCycles + a.storageCycles

||| Net cycles cost (spent - refunded)
public export
netCost : CyclesAccount -> Integer
netCost a = cast (totalSpent a) - cast a.refundCycles

-- =============================================================================
-- User cycles (attached to calls)
-- =============================================================================

||| User-attached cycles context
public export
record UserCycles where
  constructor MkUserCycles
  attached  : Nat     -- Cycles attached by user
  accepted  : Nat     -- Cycles accepted by canister
  remaining : Nat     -- Cycles remaining (to refund)

public export
Show UserCycles where
  show u = "User(attached=" ++ show u.attached ++
           ", accepted=" ++ show u.accepted ++
           ", remaining=" ++ show u.remaining ++ ")"

||| Accept cycles from user
public export
acceptUserCycles : Nat -> UserCycles -> Maybe UserCycles
acceptUserCycles amount u =
  if amount <= u.remaining
    then Just ({ accepted := u.accepted + amount
               , remaining := minus u.remaining amount } u)
    else Nothing

||| Accept all remaining user cycles
public export
acceptAllUserCycles : UserCycles -> UserCycles
acceptAllUserCycles u = { accepted := u.accepted + u.remaining, remaining := 0 } u

||| FR wrapper for accepting user cycles
public export
acceptCycles : Phase -> String -> Nat -> UserCycles -> FR UserCycles
acceptCycles phase label amount user =
  case acceptUserCycles amount user of
    Just newUser => Ok newUser (mkEvidence phase label $ "accepted " ++ show amount ++ " user cycles")
    Nothing => Fail (InsufficientCycles amount "user did not attach enough cycles")
                    (mkEvidence phase label "user cycles insufficient")
