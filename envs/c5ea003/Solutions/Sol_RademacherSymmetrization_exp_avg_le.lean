-- Prove2me | solution 1 for RademacherSymmetrization.exp_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:13.970558+00:00
-- url     : https://prove2.me/submissions/268d9aa1-7d87-488a-8d94-995224efae69

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
theorem solution(y : (Fin n → Bool) → ℝ) :
    Real.exp ((∑ ε : Fin n → Bool, y ε) / 2 ^ n)
      ≤ (∑ ε : Fin n → Bool, Real.exp (y ε)) / 2 ^ n := by
  have hw : ∀ ε ∈ (Finset.univ : Finset (Fin n → Bool)), (0:ℝ) ≤ 1 / 2 ^ n := by
    intro ε _; positivity
  have hsum : ∑ _ε : Fin n → Bool, (1:ℝ) / 2 ^ n = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    simp
  have key := ConvexOn.map_sum_le (𝕜 := ℝ) (t := (Finset.univ : Finset (Fin n → Bool)))
    (w := fun _ => 1 / (2:ℝ) ^ n) (p := y) convexOn_exp hw hsum (fun ε _ => Set.mem_univ _)
  simp only [smul_eq_mul] at key
  calc Real.exp ((∑ ε : Fin n → Bool, y ε) / 2 ^ n)
      = Real.exp (∑ ε : Fin n → Bool, (1 / (2:ℝ) ^ n) * y ε) := by
        rw [← Finset.mul_sum]; ring_nf
    _ ≤ ∑ ε : Fin n → Bool, (1 / (2:ℝ) ^ n) * Real.exp (y ε) := key
    _ = (∑ ε : Fin n → Bool, Real.exp (y ε)) / 2 ^ n := by
        rw [← Finset.mul_sum]; ring
