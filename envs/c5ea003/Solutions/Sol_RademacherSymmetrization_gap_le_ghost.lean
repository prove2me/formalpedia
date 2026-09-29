-- Prove2me | solution 1 for RademacherSymmetrization.gap_le_ghost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:15:53.896517+00:00
-- url     : https://prove2.me/submissions/8c9b2dd5-2fe8-408e-8ef6-ca248c9fe2c4

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
import Theorems.Thm_RademacherSymmetrization_sum_wt_emp
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

open RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}











/-! ### The product measure -/

omit [Fintype X] [DecidableEq X] in
lemma wt_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (S : Fin n → X) : 0 ≤ wt p S :=
  Finset.prod_nonneg fun i _ => hp (S i)

omit [DecidableEq X] in
lemma sum_wt {p : X → ℝ} (hp1 : ∑ x, p x = 1) : ∑ S : Fin n → X, wt p S = 1 := by
  classical
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => X)
      (fun _ => (Finset.univ : Finset X)) (fun _ x => p x)
  rw [Fintype.piFinset_univ] at h
  unfold wt
  rw [← h, hp1, Finset.prod_const_one]



/-! ### Step 1: introducing the ghost sample -/



/-! ### Step 2: the swapping involution -/





/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/


/-! ### A Massart bound for the empirical Rademacher complexity of a finite class

To turn the symmetrization inequality into a concrete generalization bound we bound the
empirical Rademacher complexity of a finite class of uniformly bounded functions by the
Chernoff/moment generating function argument, exactly as in Massart's finite class
lemma.
-/









open RademacherSymmetrization in
omit [DecidableEq X] in
theorem solution{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hn : 0 < n)
    (F : Finset (X → ℝ)) (hne : F.Nonempty) (S : Fin n → X) :
    gap F hne p S ≤ ∑ S' : Fin n → X, wt p S' * ghostGap F hne S S' := by
  unfold gap
  refine Finset.sup'_le _ _ fun f hf => ?_
  have hrw : mean p f - emp S f = ∑ S' : Fin n → X, wt p S' * (emp S' f - emp S f) := by
    have h1 : ∑ S' : Fin n → X, wt p S' * (emp S' f - emp S f)
        = (∑ S' : Fin n → X, wt p S' * emp S' f) - (∑ S' : Fin n → X, wt p S') * emp S f := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun S' _ => by ring
    rw [h1, sum_wt_emp hp1 hn f, sum_wt hp1, one_mul]
  rw [hrw]
  refine Finset.sum_le_sum fun S' _ => ?_
  have hle : emp S' f - emp S f ≤ ghostGap F hne S S' :=
    Finset.le_sup' (fun f => emp S' f - emp S f) hf
  exact mul_le_mul_of_nonneg_left hle (wt_nonneg hp S')
