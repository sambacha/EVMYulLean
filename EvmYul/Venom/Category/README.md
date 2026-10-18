# `EvmYul/Venom/Category/`: Venom as categories

A categorical specification of the Venom control-flow layer (`EvmYul/Venom/Cfg.lean`), following the
handoff "Venom in Lean 4: a categorical specification". Plan, results and divergences from the
handoff are in `docs/VENOM_CATEGORY_PLAN.md`. Everything is proved without `sorry`; statements
that rest on an unproved hypothesis (the SSA equivalence) take it as an explicit argument.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Flow.lean`: Flow quivers (D1.1), paths, dominance (D1.4) and P1.1: dominance is a partial order
  on reachable blocks with the entry least, and the dominators of a block form a chain
  (`Dom.antisymm`, `Dom.chain`, `domPartialOrder`, `idom_unique`).
- `FuncFlow.lean`: The flow quiver of a Venom function (one arrow per terminator slot, so parallel
  slots are parallel arrows), and the identification of `Dominance.lean`'s dominance with D1.4
  (`dominates_iff_dom`, `checkTree_dom`, `dominatesB_dom`).
- `Machine.lean`: The machine monad `StateT σ (ExceptT (Exit σ) Option)` and its Kleisli category
  (D3.1), the pointwise order on its hom-sets, environments as the presheaf `yoneda.obj Word`
  (D3.2), and the φ-copy as one precomposition (P3.1: `phiCopy_swap`, `seqCopy_swap_loses`).
- `PathSemantics.lean`: Decorations of a flow quiver and the semantics as `Paths.lift` (D3.4,
  D3.5), outcomes within a path-length bound (D3.6, D3.7), determinism.
- `Bridge.lean`: The decoration of a Venom function, and the bridge to the fuel interpreter:
  `run f (n+1)` finishes with an exit exactly when a path of length at most `n` does
  (`run_succ_iff_outcomeWithin`, settling the off-by-one), and determinism (P3.2,
  `funcDecor_deterministic`).
- `Refinement.lean`: The thin refinement category (D4.1), phases and passes as left-total
  refinement-respecting relations (D4.2), pipelines as `Paths.lift` (D4.3, `pipeline_sound`), and
  validators as lifts from the quiver of checked pairs (D4.5, `chain_sound_lift`).
- `Lifecycle.lean`: D4.6 under an explicit hypothesis that SSA construction is total and refines
  both ways: the inclusion of SSA programs is an equivalence and reflective.
- `Simulation.lean`: Lax simulations (D4.4): a prefunctor into the paths of the target and a
  lax-natural family; a simulation transports outcomes (`LaxSim.outcome`).
- `Normalization.lean`: Critical arrows, subdivision of a flow quiver and its simulation witness
  (`subdivSim`, `subdiv_outcome`), and the counterexample showing that D1.3's per-vertex
  condition is not Vyper's normal form (`vertexNormal_ne_noCritical`).
- `CfgNormalization.lean`: Critical-edge splitting on Venom functions, as Vyper's
  `CFGNormalization` does it (`normalize`), with the φs of the target redirected.
- `Retract.lean`: Parse/print as a retract in the category of partial maps (D2.1), the idempotent
  normalizer and the isomorphism of retracts with the same normalizer (P2.1), and the opcode table
  as a proved instance (`opRetract`).
- `BridgeTestHarness.lean`: Test support: a trace machine and random Venom functions.

The tests are `BridgeTests.lean`, `CfgNormalizationTests.lean`, `FlowTests.lean`,
`MachineTests.lean`, `RetractTests.lean` and `MathlibNamesTests.lean` (the audit of the Mathlib
names of the handoff's identifier map).
