-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:15.722609+00:00
-- url     : https://prove2.me/submissions/2785f867-c66f-4262-83df-5a6a952f65a7

-- Sol generated from Shared/GradedTransitivity/PolynomialGrowth.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth

/-!
# Eventually polynomial sequences have denominator `(1-q)^{r+1}`

The discrete derivative `p ↦ p(X+1) - p` lowers the degree of a polynomial.
Iterating it `r+1` times therefore annihilates every polynomial of degree `≤ r`,
and combined with `Shared.GradedTransitivity.FiniteDifference` this shows that a
sequence which is *eventually* given by a polynomial of degree `≤ r` has
generating function with denominator `(1-q)^{r+1}`.

## Main results

* `pdiff_natDegree_le` : the discrete derivative drops the degree.
* `sdiff_iter_eval_eq_zero` : `Δ^{r+1}` kills degree `≤ r` polynomial sequences.
* `exists_poly_of_eventually_polynomial` : the rationality statement.
-/

open GradedTransitivity

open Polynomial










open GradedTransitivity in
theorem solution:
    ∀ (k : ℕ) (a b : ℕ → ℚ) (N : ℕ), (∀ n ≥ N, a n = b n) →
      ∀ n ≥ N, sdiff^[k] a n = sdiff^[k] b n := by
  intro k
  induction k with
  | zero => intro a b N h n hn; simpa using h n hn
  | succ k ih =>
      intro a b N h n hn
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      refine ih (sdiff a) (sdiff b) N (fun m hm => ?_) n hn
      simp only [GradedTransitivity.sdiff, h m hm, h (m + 1) (by omega)]
