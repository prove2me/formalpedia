-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_rlhfObj_le_constrainedFreeEnergy
-- name    : NeuroSymbolicRLHF.rlhfObj_le_constrainedFreeEnergy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:48:49.94222+00:00
-- url     : https://prove2.me/theorems/8f67e9ca-4a0b-4891-87bb-cbd637efb82c
-- title:
--   Any policy supported in the admissible set scores at most the constrained
-- statement:
--   Any policy supported in the admissible set scores at most the constrained
--   free energy.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.rlhfObj_le_constrainedFreeEnergy{β : ℝ} (hβ : 0 < β) {ref r p : ι → ℝ}
--       {S : Finset ι} (href : IsPosProb ref) (hp : IsProb p) (hsupp : ∀ i ∉ S, p i = 0)
--       (hS : S.Nonempty) :
--       rlhfObj β ref r p ≤ constrainedFreeEnergy β ref r S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean#L76

-- Thm stub generated from Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
/-
# Symbolic constraints as a submodular lattice over the RLHF free energy

Third file of the neurosymbolic RLHF thread (see
`Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean`,
`MachineLearning/RLHFHilbertIsometry.lean` and
`MachineLearning/RLHFFreeEnergyDuality.lean`).

The *neurosymbolic* part of "neurosymbolic RLHF" is a hard symbolic filter: a
logical rule set restricts the admissible responses to a subset `S` of the
output space.  This file studies the induced *constrained free energy*

  `F_S(β, r) = β log ∑_{i ∈ S} ref i · exp(r i / β)`,

which we prove is exactly the optimal value of the InstructGPT objective over
policies supported in `S`.  The results bridge information theory with the
combinatorics of the Boolean lattice of constraint sets:

* **Level 0 — variational principle on a constraint set**
  (`rlhfObj_le_constrainedFreeEnergy`, `rlhfObj_constrainedGibbs`):
  `F_S` is attained, exactly, by the `S`-conditioned Gibbs policy.
* **Level 1 — commutation** (`constrainedGibbs_eq_conditional`): aligning and
  then applying the symbolic filter gives the same policy as applying the
  filter and then aligning.  Symbolic filtering and RLHF commute.
* **Level 2 — lattice structure**: `S ↦ F_S(β, r)` is *monotone*
  (`constrainedFreeEnergy_mono`) and *submodular*
  (`constrainedFreeEnergy_submodular`) on the Boolean lattice of constraint
  sets.  Submodularity is the diminishing-returns law of symbolic constraints:
  relaxing a rule helps least when other rules are already relaxed.
* **Level 3 — price of symbolic alignment**
  (`constrainedFreeEnergy_ge_sub`): the value lost by imposing the rule set `S`
  is at most `oscil r - β log ref(S)`, i.e. reward spread plus a
  `β`-weighted log-mass penalty for the pruned probability.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Constrained partition function and free energy -/






/-! ## Level 0: the constrained variational principle -/

omit [DecidableEq ι] in

theorem NeuroSymbolicRLHF.rlhfObj_le_constrainedFreeEnergy{β : ℝ} (hβ : 0 < β) {ref r p : ι → ℝ}
    {S : Finset ι} (href : IsPosProb ref) (hp : IsProb p) (hsupp : ∀ i ∉ S, p i = 0)
    (hS : S.Nonempty) :
    rlhfObj β ref r p ≤ constrainedFreeEnergy β ref r S := by sorry
