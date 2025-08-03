# Internal Contract Categories (`𝓒_C`)

This folder will eventually contain one Lean file per on-chain contract.  Each
file encodes:

1. `State`  — an abstract snapshot of the contract’s storage.
2. `Action` — an inductive type listing all externally callable functions
   (plus a catch-all for internal delegate calls where relevant).
3. `step   : Action → State → State` — pure function describing the state
   transformer.  For view/pure calls `step a σ = σ`.
4. Proofs that `Action`, equipped with:
   * identity `skip`
   * composition `;;` (run `a₁` then `a₂`)
   forms a **small category** whose objects are `State` configurations.
5. The forgetful functor `U_C` into `EVM` traces, realised by providing a
   function `compile : Action → Trace` and showing it preserves identities
   & composition.

A *generator* will parse a Solidity ABI and emit such a Lean file automatically
(see `tools/abi2lean/`, to be implemented). For now we will prototype by
hand-writing a minimal example contract. 