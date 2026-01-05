# idris2-cdk

Idris2 CDK (Canister Development Kit) for Internet Computer Protocol.

## Build

```bash
# Local build
idris2 --build idris2-cdk.ipkg

# Or with pack
pack build idris2-cdk
```

## Modules

- `ICP.IC0` - FFI boundary layer (raw ic0 system calls)
- `ICP.API` - Safe wrappers (caller, time, cycles, etc.)
- `ICP.Candid.Types` - Candid type system with `Candidable` typeclass
- `ICP.StableMemory` - `Storable` typeclass with `StableValue`/`StableSeq`
- `ICP.Management.HttpOutcall` - HTTP outcall types
- `ICP.Management.TECDSA` - Threshold ECDSA signing types

## Usage

Add to your `pack.toml`:

```toml
[custom.all.idris2-cdk]
type = "github"
url  = "https://github.com/shogochiai/idris2-cdk"
ipkg = "idris2-cdk.ipkg"
```

Import in your code:

```idris
import ICP.API
import ICP.Candid.Types
```
