-- Prove2me | solution 1 for RademacherSymmetrization.sum_wt_emp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:13:18.03076+00:00
-- url     : https://prove2.me/submissions/5de16a6c-4e69-46a3-800a-d276ca0649d2

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
import Theorems.Thm_RademacherSymmetrization_marginal
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
theorem solution{p : X → ℝ} (hp1 : ∑ x, p x = 1) (hn : 0 < n) (f : X → ℝ) :
    ∑ S : Fin n → X, wt p S * emp S f = mean p f := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  unfold emp mean
  have hstep : ∀ S : Fin n → X, wt p S * ((1 / (n:ℝ)) * ∑ i, f (S i))
      = (1 / (n:ℝ)) * ∑ i, wt p S * f (S i) := by
    intro S
    rw [← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl fun S _ => hstep S, ← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => marginal hp1 i f]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp
