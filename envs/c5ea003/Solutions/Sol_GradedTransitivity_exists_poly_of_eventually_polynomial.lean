-- Prove2me | solution 1 for GradedTransitivity.exists_poly_of_eventually_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:45:06.233399+00:00
-- url     : https://prove2.me/submissions/e0840267-99f0-48c9-93bf-c12b5b77243f

-- Sol generated from Shared/GradedTransitivity/PolynomialGrowth.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth
import Theorems.Thm_GradedTransitivity_exists_poly_pow_mul_gen
import Theorems.Thm_GradedTransitivity_sdiff_iter_congr
import Theorems.Thm_GradedTransitivity_sdiff_iter_eval_eq_zero

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
theorem solution{a : ℕ → ℚ} {r N : ℕ} {p : ℚ[X]}
    (hdeg : p.natDegree ≤ r) (hev : ∀ n ≥ N, a n = p.eval (n : ℚ)) :
    ∃ P : ℚ[X], (1 - PowerSeries.X) ^ (r + 1) * gen a = (P : PowerSeries ℚ) := by
  refine exists_poly_pow_mul_gen (r + 1) a ⟨N, fun n hn => ?_⟩
  have hc := sdiff_iter_congr (r + 1) a (fun m : ℕ => p.eval (m : ℚ)) N hev n hn
  rw [hc, sdiff_iter_eval_eq_zero r p hdeg]
