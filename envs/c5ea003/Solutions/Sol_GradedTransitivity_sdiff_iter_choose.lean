-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_choose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:23:58.927539+00:00
-- url     : https://prove2.me/submissions/0a3b0094-5300-4f44-9e30-fc852c0b77ba

-- Sol generated from Shared/GradedTransitivity/BinomialGF.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth

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




/-- **Pascal's rule as a difference equation**: `Δ C(·, r+1) = C(·, r)`. -/
theorem sdiff_choose (r : ℕ) : sdiff (chooseSeq (r + 1)) = chooseSeq r := by
  funext n
  simp only [GradedTransitivity.sdiff, chooseSeq]
  rw [Nat.choose_succ_succ n r]
  push_cast
  ring







open GradedTransitivity in
theorem solution(k : ℕ) : ∀ r : ℕ, sdiff^[k] (chooseSeq (r + k)) = chooseSeq r := by
  induction k with
  | zero => intro r; simp
  | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply]
      have : r + (k + 1) = (r + k) + 1 := by omega
      rw [this, sdiff_choose (r + k), ih r]
