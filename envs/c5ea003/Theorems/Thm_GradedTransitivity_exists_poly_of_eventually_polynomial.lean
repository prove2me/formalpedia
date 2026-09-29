-- Prove2me | Theorems.Thm_GradedTransitivity_exists_poly_of_eventually_polynomial
-- name    : GradedTransitivity.exists_poly_of_eventually_polynomial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:45.685988+00:00
-- url     : https://prove2.me/theorems/596963e1-3e45-4d62-ade8-87296d7abcc1
-- title:
--   **Eventually polynomial sequences are rational with denominator
-- statement:
--   **Eventually polynomial sequences are rational with denominator
--   `(1-q)^{r+1}`.** If `a n = p(n)` for all large `n` and `deg p â¤ r`, then
--   `(1-q)^{r+1} â a n qâ¿` is a polynomial.
--
--   ```lean
--   theorem GradedTransitivity.exists_poly_of_eventually_polynomial{a : ℕ → ℚ} {r N : ℕ} {p : ℚ[X]}
--       (hdeg : p.natDegree ≤ r) (hev : ∀ n ≥ N, a n = p.eval (n : ℚ)) :
--       ∃ P : ℚ[X], (1 - PowerSeries.X) ^ (r + 1) * gen a = (P : PowerSeries ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/PolynomialGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/PolynomialGrowth.lean#L99

-- Thm stub generated from Shared/GradedTransitivity/PolynomialGrowth.lean
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

theorem GradedTransitivity.exists_poly_of_eventually_polynomial{a : ℕ → ℚ} {r N : ℕ} {p : ℚ[X]}
    (hdeg : p.natDegree ≤ r) (hev : ∀ n ≥ N, a n = p.eval (n : ℚ)) :
    ∃ P : ℚ[X], (1 - PowerSeries.X) ^ (r + 1) * gen a = (P : PowerSeries ℚ) := by sorry
