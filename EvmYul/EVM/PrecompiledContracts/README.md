# `EvmYul/EVM/PrecompiledContracts/`: Precompiled contracts

One module per precompile wrapper, and `Contracts.lean`, the dispatch table `Ξ_…` by address.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Blake2F.lean`: Precompile `BLAKE2_F` (address 0x09).
- `BnAdd.lean`: Precompile `BN_ADD` (address 0x06).
- `BnMul.lean`: Precompile `BN_MUL` (address 0x07).
- `Contracts.lean`: The precompiled contracts `Ξ_…`.
- `PointEval.lean`: Precompile `POINT_EVALUATION` (address 0x0a).
- `Ripemd160.lean`: Precompile `RIPEMD-160` (address 0x03).
- `Sha256.lean`: Precompile `SHA2-256` (address 0x02).
- `Snarkv.lean`: Precompile `SNARKV` (address 0x08).
