-- Prove2me | Theorems.Thm_GradedTransitivity_pdiff_natDegree_le
-- name    : GradedTransitivity.pdiff_natDegree_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:24.787896+00:00
-- url     : https://prove2.me/theorems/0091b4f2-2fe7-4f97-a748-5ddcc7826fa9
-- title:
--   The discrete derivative strictly lowers the degree: if `deg p â¤ d+1` then
-- statement:
--   The discrete derivative strictly lowers the degree: if `deg p â¤ d+1` then
--   `deg (Îp) â¤ d`.
--
--   ```lean
--   theorem GradedTransitivity.pdiff_natDegree_le{p : ℚ[X]} {d : ℕ} (hp : p.natDegree ≤ d + 1) :
--       (pdiff p).natDegree ≤ d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/PolynomialGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/PolynomialGrowth.lean#L28

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

theorem GradedTransitivity.pdiff_natDegree_le{p : ℚ[X]} {d : ℕ} (hp : p.natDegree ≤ d + 1) :
    (pdiff p).natDegree ≤ d := by sorry
