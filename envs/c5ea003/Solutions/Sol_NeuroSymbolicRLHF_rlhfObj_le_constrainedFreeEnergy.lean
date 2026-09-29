-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhfObj_le_constrainedFreeEnergy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:33:44.306719+00:00
-- url     : https://prove2.me/submissions/9fe091fa-5aed-49d5-93bd-c85beb0201e3

-- Sol generated from Speculative/AutoResearch/RLHFSymbolicConstraintLattice.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
import Theorems.Thm_NeuroSymbolicRLHF_term_le
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




/-! ## Level 1: symbolic filtering commutes with alignment -/


/-! ## Level 2: monotonicity and submodularity over the constraint lattice -/



/-! ## Level 3: the price of symbolic alignment -/



open NeuroSymbolicRLHF in
omit [DecidableEq ι] in
theorem solution{β : ℝ} (hβ : 0 < β) {ref r p : ι → ℝ}
    {S : Finset ι} (href : IsPosProb ref) (hp : IsProb p) (hsupp : ∀ i ∉ S, p i = 0)
    (hS : S.Nonempty) :
    rlhfObj β ref r p ≤ constrainedFreeEnergy β ref r S := by
  set W := constrainedZ β ref r S with hW
  have hWpos : 0 < W := constrainedZ_pos href hS
  set w : ι → ℝ := fun i => ref i * Real.exp (r i / β) with hw
  have hwpos : ∀ i, 0 < w i := fun i => mul_pos (href.pos i) (Real.exp_pos _)
  -- mass on the admissible set is one
  have hpS : ∑ i ∈ S, p i = 1 := by
    rw [← hp.sum_one]
    exact Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => hsupp i hiS
  -- Gibbs inequality on `S` against the normalised tilted measure
  have hgibbs : 0 ≤ ∑ i ∈ S, p i * Real.log (p i / (w i / W)) := by
    have hterm : ∀ i ∈ S, p i - w i / W ≤ p i * Real.log (p i / (w i / W)) := by
      intro i _
      exact term_le _ _ (hp.nonneg i) (div_pos (hwpos i) hWpos)
    have hsum := Finset.sum_le_sum hterm
    have hleft : ∑ i ∈ S, (p i - w i / W) = 0 := by
      have hWsum : ∑ i ∈ S, w i = W := rfl
      rw [Finset.sum_sub_distrib, hpS, ← Finset.sum_div, hWsum, div_self hWpos.ne', sub_self]
    linarith [hleft ▸ hsum]
  -- rewrite the objective as a KL against the tilted measure
  have hkl : klDivFin p ref = ∑ i ∈ S, p i * Real.log (p i / ref i) := by
    simp only [klDivFin]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => ?_).symm
    simp [hsupp i hiS]
  have hrew : ∑ i, p i * r i = ∑ i ∈ S, p i * r i := by
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hiS => ?_).symm
    simp [hsupp i hiS]
  have hsplit : ∀ i ∈ S, p i * Real.log (p i / (w i / W))
      = p i * Real.log (p i / ref i) - p i * (r i / β) + p i * Real.log W := by
    intro i _
    rcases eq_or_lt_of_le (hp.nonneg i) with h | h
    · simp [← h]
    · have h1 : p i / (w i / W) = (p i / ref i) * (Real.exp (-(r i / β)) * W) := by
        simp only [hw]
        rw [Real.exp_neg]
        field_simp
      rw [h1, Real.log_mul (div_pos h (href.pos i)).ne'
          (mul_pos (Real.exp_pos _) hWpos).ne',
        Real.log_mul (Real.exp_pos _).ne' hWpos.ne', Real.log_exp]
      ring
  have hcalc : ∑ i ∈ S, p i * Real.log (p i / (w i / W))
      = klDivFin p ref - (∑ i ∈ S, p i * r i) / β + Real.log W := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hpS, one_mul, hkl]
    congr 1
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hcalc] at hgibbs
  simp only [rlhfObj, constrainedFreeEnergy, ← hW, hrew]
  have hmul : β * (klDivFin p ref - (∑ i ∈ S, p i * r i) / β + Real.log W) ≥ 0 :=
    mul_nonneg hβ.le hgibbs
  have hexp : β * (klDivFin p ref - (∑ i ∈ S, p i * r i) / β + Real.log W)
      = β * klDivFin p ref - (∑ i ∈ S, p i * r i) + β * Real.log W := by
    field_simp
  linarith [hexp ▸ hmul]
