-- Prove2me | solution 1 for GradedTransitivity.binomial_generating_function
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:12.750988+00:00
-- url     : https://prove2.me/submissions/a40a874d-0498-46b1-a213-a47fb385beff

-- Sol generated from Shared/GradedTransitivity/BinomialGF.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth
import Theorems.Thm_GradedTransitivity_coeff_gen
import Theorems.Thm_GradedTransitivity_one_sub_X_mul_gen

/-!
# The binomial generating function and sharpness of the exponent `r+1`

The sequence `n ↦ C(n, r)` is the universal example of polynomial growth of
degree exactly `r`.  Here we compute its generating function *exactly*,

`∑_{n} C(n,r) qⁿ = q^r / (1-q)^{r+1}`,

purely from the Pascal recurrence, and we deduce that the exponent `r+1` in
`Shared.GradedTransitivity.PolynomialGrowth` cannot be lowered: for this
sequence `(1-q)^r ∑ C(n,r) qⁿ` is *not* a polynomial.

## Main results

* `sdiff_choose` : Pascal's rule as a statement about forward differences.
* `binomial_generating_function` : `(1-X)^{r+1} ∑ C(n,r) Xⁿ = X^r`.
* `binomial_denominator_sharp` : the exponent `r+1` is optimal.
-/

open GradedTransitivity

open Polynomial


@[simp] lemma chooseSeq_zero_index (r : ℕ) : chooseSeq (r + 1) 0 = 0 := by
  simp [chooseSeq]

@[simp] lemma chooseSeq_zero : chooseSeq 0 = fun _ => (1 : ℚ) := by
  funext n; simp [chooseSeq]

/-- **Pascal's rule as a difference equation**: `Δ C(·, r+1) = C(·, r)`. -/
theorem sdiff_choose (r : ℕ) : sdiff (chooseSeq (r + 1)) = chooseSeq r := by
  funext n
  simp only [GradedTransitivity.sdiff, chooseSeq]
  rw [Nat.choose_succ_succ n r]
  push_cast
  ring







open GradedTransitivity in
theorem solution(r : ℕ) :
    (1 - PowerSeries.X) ^ (r + 1) * gen (chooseSeq r) = (PowerSeries.X : PowerSeries ℚ) ^ r := by
  induction r with
  | zero =>
      rw [pow_one, one_sub_X_mul_gen]
      have h1 : sdiff (chooseSeq 0) = fun _ => (0 : ℚ) := by
        funext n; simp [GradedTransitivity.sdiff]
      have h2 : gen (fun _ : ℕ => (0 : ℚ)) = 0 := by
        ext n; simp
      rw [h1, h2]
      simp [chooseSeq]
  | succ r ih =>
      have hsplit : (1 - PowerSeries.X) ^ (r + 1 + 1) * gen (chooseSeq (r + 1))
          = (1 - PowerSeries.X) ^ (r + 1) * ((1 - PowerSeries.X) * gen (chooseSeq (r + 1))) := by
        ring
      rw [hsplit, one_sub_X_mul_gen, sdiff_choose r, chooseSeq_zero_index]
      rw [map_zero, add_zero, ← mul_assoc, mul_comm ((1 - PowerSeries.X) ^ (r + 1)) PowerSeries.X,
        mul_assoc, ih, pow_succ, mul_comm]
