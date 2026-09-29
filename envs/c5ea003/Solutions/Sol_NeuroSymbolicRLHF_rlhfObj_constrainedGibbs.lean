-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhfObj_constrainedGibbs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:33:43.841767+00:00
-- url     : https://prove2.me/submissions/54babf38-fea7-4f44-9d20-a4b091857370

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


/-! ## Level 0: the constrained variational principle -/


theorem constrainedGibbs_isProb {β : ℝ} {ref r : ι → ℝ} {S : Finset ι} (href : IsPosProb ref)
    (hS : S.Nonempty) : IsProb (constrainedGibbs β ref r S) := by
  have hWpos : 0 < constrainedZ β ref r S := constrainedZ_pos href hS
  refine ⟨fun i => ?_, ?_⟩
  · simp only [constrainedGibbs]
    split
    · exact (div_pos (mul_pos (href.pos i) (Real.exp_pos _)) hWpos).le
    · exact le_rfl
  · simp only [constrainedGibbs]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
    exact div_self hWpos.ne'


/-! ## Level 1: symbolic filtering commutes with alignment -/


/-! ## Level 2: monotonicity and submodularity over the constraint lattice -/



/-! ## Level 3: the price of symbolic alignment -/



open NeuroSymbolicRLHF in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} {S : Finset ι}
    (href : IsPosProb ref) (hS : S.Nonempty) :
    rlhfObj β ref r (constrainedGibbs β ref r S) = constrainedFreeEnergy β ref r S := by
  have hWpos : 0 < constrainedZ β ref r S := constrainedZ_pos href hS
  have hqval : ∀ i ∈ S, constrainedGibbs β ref r S i
      = ref i * Real.exp (r i / β) / constrainedZ β ref r S := by
    intro i hi
    simp [constrainedGibbs, hi]
  have hqzero : ∀ i ∉ S, constrainedGibbs β ref r S i = 0 := by
    intro i hi
    simp [constrainedGibbs, hi]
  have hqsum : ∑ i ∈ S, constrainedGibbs β ref r S i = 1 := by
    rw [← (constrainedGibbs_isProb (β := β) (r := r) href hS).sum_one]
    exact Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => hqzero i hiS
  have hrew : ∑ i, constrainedGibbs β ref r S i * r i
      = ∑ i ∈ S, constrainedGibbs β ref r S i * r i :=
    (Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => by simp [hqzero i hiS]).symm
  have hkl : klDivFin (constrainedGibbs β ref r S) ref
      = ∑ i ∈ S, constrainedGibbs β ref r S i
          * Real.log (constrainedGibbs β ref r S i / ref i) := by
    simp only [klDivFin]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => ?_).symm
    simp [hqzero i hiS]
  have hlog : ∀ i ∈ S, constrainedGibbs β ref r S i
        * Real.log (constrainedGibbs β ref r S i / ref i)
      = constrainedGibbs β ref r S i * (r i / β)
        - constrainedGibbs β ref r S i * Real.log (constrainedZ β ref r S) := by
    intro i hi
    have hri : ref i ≠ 0 := (href.pos i).ne'
    have hqi : constrainedGibbs β ref r S i / ref i
        = Real.exp (r i / β) / constrainedZ β ref r S := by
      rw [hqval i hi]
      field_simp
    rw [hqi, Real.log_div (Real.exp_pos _).ne' hWpos.ne', Real.log_exp]
    ring
  have hklval : klDivFin (constrainedGibbs β ref r S) ref
      = (∑ i ∈ S, constrainedGibbs β ref r S i * r i) / β
        - Real.log (constrainedZ β ref r S) := by
    rw [hkl, Finset.sum_congr rfl hlog, Finset.sum_sub_distrib, ← Finset.sum_mul, hqsum, one_mul]
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [rlhfObj, constrainedFreeEnergy, hrew, hklval]
  field_simp
  ring
