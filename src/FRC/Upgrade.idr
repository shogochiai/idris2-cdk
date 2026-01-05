||| Canister Upgrade and Migration Patterns
|||
||| ICP canisters undergo upgrades that require state migration.
||| This module provides FR-aware patterns for safe upgrades.
|||
||| Key concerns:
||| - PreUpgrade: serialize state to stable memory
||| - PostUpgrade: restore state from stable memory
||| - Version migration: handle schema changes
||| - Rollback: recover from failed upgrades
module FRC.Upgrade

import FRC.Conflict
import FRC.Evidence
import FRC.Outcome

%default total

-- =============================================================================
-- Version Management
-- =============================================================================

||| Canister version with major.minor.patch
public export
record Version where
  constructor MkVersion
  major : Nat
  minor : Nat
  patch : Nat

public export
Show Version where
  show v = show v.major ++ "." ++ show v.minor ++ "." ++ show v.patch

public export
Eq Version where
  v1 == v2 = v1.major == v2.major && v1.minor == v2.minor && v1.patch == v2.patch

public export
Ord Version where
  compare v1 v2 =
    case compare v1.major v2.major of
      EQ => case compare v1.minor v2.minor of
              EQ => compare v1.patch v2.patch
              x  => x
      x  => x

||| Check if upgrade is compatible (same major version)
public export
isCompatible : Version -> Version -> Bool
isCompatible v1 v2 = v1.major == v2.major

||| Check if migration is needed (different version)
public export
needsMigration : Version -> Version -> Bool
needsMigration v1 v2 = v1 /= v2

-- =============================================================================
-- Migration Types
-- =============================================================================

||| Migration direction
public export
data MigrationDir
  = Upgrade      -- Old version -> New version
  | Downgrade    -- New version -> Old version (rollback)

public export
Show MigrationDir where
  show Upgrade   = "UPGRADE"
  show Downgrade = "DOWNGRADE"

||| Migration step definition
public export
record MigrationStep where
  constructor MkMigrationStep
  fromVersion : Version
  toVersion   : Version
  direction   : MigrationDir
  description : String

public export
Show MigrationStep where
  show m = show m.fromVersion ++ " -> " ++ show m.toVersion ++
           " [" ++ show m.direction ++ "] " ++ m.description

-- =============================================================================
-- Upgrade State Machine
-- =============================================================================

||| Upgrade lifecycle state
public export
data UpgradeState
  = Running              -- Normal operation
  | PreUpgrading         -- Serializing state
  | Upgrading            -- Between pre and post upgrade
  | PostUpgrading        -- Restoring state
  | Failed String        -- Upgrade failed with reason

public export
Show UpgradeState where
  show Running       = "RUNNING"
  show PreUpgrading  = "PRE_UPGRADING"
  show Upgrading     = "UPGRADING"
  show PostUpgrading = "POST_UPGRADING"
  show (Failed r)    = "FAILED: " ++ r

public export
Eq UpgradeState where
  Running       == Running       = True
  PreUpgrading  == PreUpgrading  = True
  Upgrading     == Upgrading     = True
  PostUpgrading == PostUpgrading = True
  Failed r1     == Failed r2     = r1 == r2
  _ == _ = False

||| Check if canister is in upgrade process
public export
isUpgrading : UpgradeState -> Bool
isUpgrading Running       = False
isUpgrading PreUpgrading  = True
isUpgrading Upgrading     = True
isUpgrading PostUpgrading = True
isUpgrading (Failed _)    = False

-- =============================================================================
-- Upgrade Context
-- =============================================================================

||| Context for upgrade operations
public export
record UpgradeContext where
  constructor MkUpgradeContext
  currentVersion : Version
  targetVersion  : Version
  state          : UpgradeState
  stableSize     : Nat           -- Bytes in stable memory
  startTime      : Nat           -- Upgrade start timestamp

public export
Show UpgradeContext where
  show ctx = "Upgrade(" ++ show ctx.currentVersion ++ " -> " ++
             show ctx.targetVersion ++ ", " ++ show ctx.state ++ ")"

||| Create upgrade context
public export
mkUpgradeContext : Version -> Version -> UpgradeContext
mkUpgradeContext current target = MkUpgradeContext current target Running 0 0

-- =============================================================================
-- FR-aware Upgrade Operations
-- =============================================================================

||| Begin upgrade (transition to PreUpgrading)
public export
beginUpgrade : UpgradeContext -> FR UpgradeContext
beginUpgrade ctx =
  case ctx.state of
    Running => Ok ({ state := PreUpgrading } ctx)
                  (mkEvidence PreUpgrade "beginUpgrade" "started pre-upgrade")
    _       => Fail (InvalidState $ "cannot begin upgrade in state " ++ show ctx.state)
                    (mkEvidence PreUpgrade "beginUpgrade" "invalid state")

||| Complete pre-upgrade (transition to Upgrading)
public export
completePreUpgrade : UpgradeContext -> Nat -> FR UpgradeContext
completePreUpgrade ctx stableBytes =
  case ctx.state of
    PreUpgrading => Ok ({ state := Upgrading, stableSize := stableBytes } ctx)
                       (mkEvidence PreUpgrade "completePreUpgrade" $
                        "serialized " ++ show stableBytes ++ " bytes")
    _            => Fail (InvalidState $ "expected PreUpgrading, got " ++ show ctx.state)
                         (mkEvidence PreUpgrade "completePreUpgrade" "invalid state")

||| Begin post-upgrade (transition to PostUpgrading)
public export
beginPostUpgrade : UpgradeContext -> FR UpgradeContext
beginPostUpgrade ctx =
  case ctx.state of
    Upgrading => Ok ({ state := PostUpgrading } ctx)
                    (mkEvidence PostUpgrade "beginPostUpgrade" "started post-upgrade")
    _         => Fail (InvalidState $ "expected Upgrading, got " ++ show ctx.state)
                      (mkEvidence PostUpgrade "beginPostUpgrade" "invalid state")

||| Complete upgrade (transition to Running with new version)
public export
completeUpgrade : UpgradeContext -> FR UpgradeContext
completeUpgrade ctx =
  case ctx.state of
    PostUpgrading => Ok ({ state := Running, currentVersion := ctx.targetVersion } ctx)
                        (mkEvidence PostUpgrade "completeUpgrade" $
                         "upgraded to " ++ show ctx.targetVersion)
    _             => Fail (InvalidState $ "expected PostUpgrading, got " ++ show ctx.state)
                          (mkEvidence PostUpgrade "completeUpgrade" "invalid state")

||| Mark upgrade as failed
public export
failUpgrade : String -> UpgradeContext -> FR UpgradeContext
failUpgrade reason ctx =
  Ok ({ state := Failed reason } ctx)
     (mkEvidence (if ctx.state == PreUpgrading then PreUpgrade else PostUpgrade)
                 "failUpgrade" reason)

-- =============================================================================
-- Version Checks
-- =============================================================================

||| Require specific version
public export
requireVersion : Version -> Version -> FR ()
requireVersion expected actual =
  if expected == actual
    then Ok () (mkEvidence Update "requireVersion" $ "version " ++ show actual ++ " OK")
    else Fail (VersionMismatch expected.major actual.major)
              (mkEvidence Update "requireVersion" $
               "expected " ++ show expected ++ ", got " ++ show actual)

||| Require compatible version (same major)
public export
requireCompatible : Version -> Version -> FR ()
requireCompatible expected actual =
  if isCompatible expected actual
    then Ok () (mkEvidence Update "requireCompatible" "versions compatible")
    else Fail (VersionMismatch expected.major actual.major)
              (mkEvidence Update "requireCompatible" "incompatible major version")

||| Require version at least
public export
requireMinVersion : Version -> Version -> FR ()
requireMinVersion minVer actual =
  if actual >= minVer
    then Ok () (mkEvidence Update "requireMinVersion" $ "version " ++ show actual ++ " >= " ++ show minVer)
    else Fail (VersionMismatch minVer.major actual.major)
              (mkEvidence Update "requireMinVersion" $
               "version " ++ show actual ++ " < minimum " ++ show minVer)

-- =============================================================================
-- Migration Combinators
-- =============================================================================

||| Migration function type
public export
Migration : Type -> Type -> Type
Migration old new = old -> FR new

||| Chain migrations
public export
chainMigrations : Migration a b -> Migration b c -> Migration a c
chainMigrations f g x = f x >>= g

||| Optional migration (run if versions differ)
public export
migrateIf : Version -> Version -> Migration a a -> Migration a a
migrateIf from to migration x =
  if needsMigration from to
    then migration x
    else Ok x (mkEvidence PostUpgrade "migrateIf" "no migration needed")

||| Migration with rollback support
public export
migrateWithRollback : Migration a b -> Migration b a -> a -> FR (b, Migration b a)
migrateWithRollback forward rollback x = do
  result <- forward x
  pure (result, rollback)

-- =============================================================================
-- Stable Memory Patterns
-- =============================================================================

||| Stable memory region descriptor
public export
record StableRegion where
  constructor MkStableRegion
  offset : Nat      -- Start offset in stable memory
  size   : Nat      -- Size in bytes
  tag    : String   -- Region identifier

public export
Show StableRegion where
  show r = "StableRegion(" ++ r.tag ++ " @" ++ show r.offset ++ ", " ++ show r.size ++ " bytes)"

||| Stable memory layout
public export
record StableLayout where
  constructor MkStableLayout
  version     : Version
  regions     : List StableRegion
  totalSize   : Nat
  checksum    : Nat          -- For integrity verification

||| Validate stable memory layout
public export
validateLayout : StableLayout -> Nat -> FR ()
validateLayout layout availableBytes =
  if layout.totalSize <= availableBytes
    then Ok () (mkEvidence PostUpgrade "validateLayout" "layout fits in stable memory")
    else Fail (StableMemError $ "layout requires " ++ show layout.totalSize ++
               " bytes but only " ++ show availableBytes ++ " available")
              (mkEvidence PostUpgrade "validateLayout" "insufficient stable memory")

-- =============================================================================
-- Upgrade Guards
-- =============================================================================

||| Guard: only run if upgrading
public export
onlyDuringUpgrade : UpgradeContext -> FR ()
onlyDuringUpgrade ctx =
  if isUpgrading ctx.state
    then Ok () (mkEvidence Update "onlyDuringUpgrade" "in upgrade mode")
    else Fail (InvalidState "operation only allowed during upgrade")
              (mkEvidence Update "onlyDuringUpgrade" "not in upgrade mode")

||| Guard: only run if NOT upgrading
public export
notDuringUpgrade : UpgradeContext -> FR ()
notDuringUpgrade ctx =
  if not (isUpgrading ctx.state)
    then Ok () (mkEvidence Update "notDuringUpgrade" "not in upgrade mode")
    else Fail (InvalidState "operation not allowed during upgrade")
              (mkEvidence Update "notDuringUpgrade" "in upgrade mode")

||| Guard: check upgrade not failed
public export
upgradeNotFailed : UpgradeContext -> FR ()
upgradeNotFailed ctx =
  case ctx.state of
    Failed reason => Fail (UpgradeFailed reason)
                          (mkEvidence Update "upgradeNotFailed" "upgrade already failed")
    _             => Ok () (mkEvidence Update "upgradeNotFailed" "upgrade not failed")
