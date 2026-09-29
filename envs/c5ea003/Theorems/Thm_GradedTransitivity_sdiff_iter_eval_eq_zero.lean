-- Prove2me | Theorems.Thm_GradedTransitivity_sdiff_iter_eval_eq_zero
-- name    : GradedTransitivity.sdiff_iter_eval_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:32.170962+00:00
-- url     : https://prove2.me/theorems/db127277-6920-4bb2-99da-934a32ae928d
-- title:
--   `Î^{d+1}` annihilates every polynomial sequence of degree `â¤ d`.
-- statement:
--   `Î^{d+1}` annihilates every polynomial sequence of degree `â¤ d`.
--
--   ```lean
--   theorem GradedTransitivity.sdiff_iter_eval_eq_zero:
--       ∀ (d : ℕ) (p : ℚ[X]), p.natDegree ≤ d →
--         sdiff^[d + 1] (fun n : ℕ => p.eval (n : ℚ)) = fun _ => 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/PolynomialGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/PolynomialGrowth.lean#L65

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

theorem GradedTransitivity.sdiff_iter_eval_eq_zero:
    ∀ (d : ℕ) (p : ℚ[X]), p.natDegree ≤ d →
      sdiff^[d + 1] (fun n : ℕ => p.eval (n : ℚ)) = fun _ => 0 := by sorry
