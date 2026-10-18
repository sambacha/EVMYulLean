# `EvmYul/Venom/`: Venom

The Venom IR of the Vyper compiler.
- The straight-line fragment: syntax, semantics with gas, a compiler to EVM code with a correctness proof, and the assembler.
- A proved checker for lowerings to stack code that use `SWAP` and `POP`.
- The control-flow-graph layer (blocks, φ, refinement), with machine interfaces backed by the project's EVM.
- A proved checker for whole functions lowered to stack code: stack layouts across blocks and φs resolved at block edges, and the bytecode of whole functions.
- A parser and printer for Venom text, and a checked dominator tree with a strict-SSA check.

The review and plan behind the lowering checker and the CFG layer are in `docs/VENOM_LOWERING_PLAN.md`; the plan for the cross-block checker, the EVM-backed interfaces and the gas bounds is in `docs/VENOM_REMAINING_PLAN.md`.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Assemble.lean`: Assembling compiled Venom code, a byte-level reference model, and the run on `Θ`.
  - Also assembles stack code with `SWAP`/`POP` (`assembleS`, `assembleS_embed`) and whole stack functions with their jumps (`assembleCfg`).
- `BlockLowering.lean`: Lowering control-flow graphs to stack code: stack layouts across blocks and φs at block edges.
  - The function checker `checkCfg` is proved sound for every fuel: `checkCfg_sound`.
  - The block runners are `run` and `runSAsm` on one block: `run_eq_runBody`, `runSAsm_eq_runSBody`.
- `Category/`: A categorical specification of Venom: the flow quiver and dominance, the semantics as a functor out of the path category, refinement, simulations, critical-edge splitting and the parse/print retract (plan and results in `docs/VENOM_CATEGORY_PLAN.md`).
- `Cfg.lean`: Venom control-flow graphs.
  - Covers blocks, φ as a parallel copy, fuel semantics, and refinement.
  - It is the root-level sketch `Venom.lean` as a library module, with its corrections: `RefinesIn`, `RefinesTotal` and `Func.wf`.
  - Proves fuel stability and determinism.
  - Gives `djmp` its meaning with label addresses (`runL`, `execTermL_djmp_iff`), a conservative extension of `run` (`runL_noAddr`).
- `Compile.lean`: Compiling the Venom straight-line fragment to EVM stack code, with a correctness proof.
- `Dominance.lean`: Dominance in Venom control-flow graphs: a checked dominator tree and a strict-SSA check.
  - The tree is computed untrusted and checked as a certificate; `checkTree_sound` proves that every tree ancestor dominates (every path from the entry passes through it).
  - `checkSSA_sound`: every use is defined earlier in its block or in a dominating block.
- `EvmMachine.lean`: The Venom machine interfaces backed by the project's EVM.
  - Every primitive runs through `EVM.step` (`execOp`): `evmPrims` for the straight-line fragment, `evmInterface` for the CFG layer.
- `LoweringCheck.lean`: A checker for lowerings of the straight-line fragment to stack code with `SWAP`/`POP`.
  - Soundness is proved: `validateLowering_sound`.
  - The scheduler that produces the code stays untrusted.
- `Semantics.lean`: Venom IR: big-step semantics of the straight-line fragment, with gas.
- `Text.lean`: A parser and a printer for Venom text (`vyper -f bb_runtime`) over the CFG layer.
  - The opcode table round-trips (`opOfName?_opName`); whole functions are round-trip tested on random functions and on recorded Vyper output.
- `StackLowering.lean`: Lowering whole functions of the control-flow-graph language to stack code.
  - Covers φs, every machine opcode through the machine interface (`assign`, `codecopy`, multi-result instructions), labels used as values, `assert`, and `jmp`/`jnz`/`djmp`.
  - The checker `checkFunc` is proved sound for every fuel, machine and label-address map: `checkFunc_sound`, `checkFunc_refines`.
- `Syntax.lean`: Venom IR: the straight-line fragment (syntax and pure operations).
