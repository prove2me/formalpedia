-- Prove2me | solution 1 for NeuroSymbolicRLHF.constrainedFreeEnergy_submodular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:10:55.905416+00:00
-- url     : https://prove2.me/submissions/9cc906c3-53f2-4428-85b3-6f8428492ec6

-- Sol generated from Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean
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




omit [DecidableEq ι] in
theorem constrainedZ_pos {β : ℝ} {ref r : ι → ℝ} {S : Finset ι} (href : IsPosProb ref)
    (hS : S.Nonempty) : 0 < constrainedZ β ref r S := by
  refine Finset.sum_pos (fun i _ => mul_pos (href.pos i) (Real.exp_pos _)) hS

omit [DecidableEq ι] in
theorem constrainedZ_le_of_subset {β : ℝ} {ref r : ι → ℝ} {S T : Finset ι}
    (href : IsPosProb ref) (hST : S ⊆ T) :
    constrainedZ β ref r S ≤ constrainedZ β ref r T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST
    fun i _ _ => mul_nonneg (href.pos i).le (Real.exp_pos _).le

/-! ## Level 0: the constrained variational principle -/




/-! ## Level 1: symbolic filtering commutes with alignment -/


/-! ## Level 2: monotonicity and submodularity over the constraint lattice -/



/-! ## Level 3: the price of symbolic alignment -/



open NeuroSymbolicRLHF in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} {S T : Finset ι}
    (href : IsPosProb ref) (hST : (S ∩ T).Nonempty) :
    constrainedFreeEnergy β ref r (S ∪ T) + constrainedFreeEnergy β ref r (S ∩ T)
      ≤ constrainedFreeEnergy β ref r S + constrainedFreeEnergy β ref r T := by
  have hIpos : 0 < constrainedZ β ref r (S ∩ T) := constrainedZ_pos href hST
  have hSpos : 0 < constrainedZ β ref r S :=
    constrainedZ_pos href (hST.mono Finset.inter_subset_left)
  have hTpos : 0 < constrainedZ β ref r T :=
    constrainedZ_pos href (hST.mono Finset.inter_subset_right)
  have hUpos : 0 < constrainedZ β ref r (S ∪ T) :=
    constrainedZ_pos href (hST.mono (Finset.inter_subset_union))
  -- modularity of the partition function
  have hmod : constrainedZ β ref r (S ∪ T) + constrainedZ β ref r (S ∩ T)
      = constrainedZ β ref r S + constrainedZ β ref r T := by
    simpa [constrainedZ] using
      Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := fun i => ref i * Real.exp (r i / β))
  have hIS : constrainedZ β ref r (S ∩ T) ≤ constrainedZ β ref r S :=
    constrainedZ_le_of_subset href Finset.inter_subset_left
  have hIT : constrainedZ β ref r (S ∩ T) ≤ constrainedZ β ref r T :=
    constrainedZ_le_of_subset href Finset.inter_subset_right
  -- the key inequality `Z_{S∪T} Z_{S∩T} ≤ Z_S Z_T`
  have hprod : constrainedZ β ref r (S ∪ T) * constrainedZ β ref r (S ∩ T)
      ≤ constrainedZ β ref r S * constrainedZ β ref r T := by
    nlinarith [hIS, hIT, hmod]
  have hlog := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul hUpos.ne' hIpos.ne', Real.log_mul hSpos.ne' hTpos.ne'] at hlog
  simp only [constrainedFreeEnergy]
  nlinarith [mul_le_mul_of_nonneg_left hlog hβ.le]
