-- Prove2me | Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
-- name    : Speculative_AutoResearch_RLHFSymbolicConstraintLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:25.58195+00:00
-- url     : https://prove2.me/theorems/778b6755-d462-425f-bc4d-16886322edd4
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_RLHFSymbolicConstraintLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.RLHFSymbolicConstraintLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean by skeleton subtraction
import Mathlib
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

namespace NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Constrained partition function and free energy -/

/-- Partition function restricted to the symbolically admissible set `S`. -/
def constrainedZ (β : ℝ) (ref r : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, ref i * Real.exp (r i / β)

/-- Free energy of the RLHF objective restricted to policies supported in `S`. -/
def constrainedFreeEnergy (β : ℝ) (ref r : ι → ℝ) (S : Finset ι) : ℝ :=
  β * Real.log (constrainedZ β ref r S)

/-- The `S`-conditioned Gibbs policy: the exponentially tilted policy
renormalised over the admissible set. -/
def constrainedGibbs (β : ℝ) (ref r : ι → ℝ) (S : Finset ι) : ι → ℝ :=
  fun i => if i ∈ S then ref i * Real.exp (r i / β) / constrainedZ β ref r S else 0



/-! ## Level 0: the constrained variational principle -/




/-! ## Level 1: symbolic filtering commutes with alignment -/


/-! ## Level 2: monotonicity and submodularity over the constraint lattice -/



/-! ## Level 3: the price of symbolic alignment -/


end NeuroSymbolicRLHF


