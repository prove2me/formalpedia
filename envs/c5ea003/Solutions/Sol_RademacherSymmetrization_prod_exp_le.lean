-- Prove2me | solution 1 for RademacherSymmetrization.prod_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:56.696748+00:00
-- url     : https://prove2.me/submissions/f8d502e2-5356-46ba-b685-4754c2c837c2

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
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
omit [Fintype X] [DecidableEq X] in
theorem solution(v : Fin n → ℝ) (l : ℝ) :
    ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
      ≤ 2 ^ n * Real.exp (l ^ 2 * (∑ i, (v i) ^ 2) / 2) := by
  have hstep : ∀ i : Fin n, Real.exp (l * v i) + Real.exp (-(l * v i))
      ≤ 2 * Real.exp ((l * v i) ^ 2 / 2) := by
    intro i
    have h := Real.cosh_le_exp_half_sq (l * v i)
    rw [Real.cosh_eq] at h
    linarith
  calc ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
      ≤ ∏ i, (2 * Real.exp ((l * v i) ^ 2 / 2)) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hstep i)
    _ = 2 ^ n * ∏ i, Real.exp ((l * v i) ^ 2 / 2) := by
        rw [Finset.prod_mul_distrib]; simp
    _ = 2 ^ n * Real.exp (∑ i, (l * v i) ^ 2 / 2) := by rw [Real.exp_sum]
    _ = 2 ^ n * Real.exp (l ^ 2 * (∑ i, (v i) ^ 2) / 2) := by
        congr 2
        rw [Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
