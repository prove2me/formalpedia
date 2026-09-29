-- Prove2me | Theorems.Thm_GradedTransitivity_exists_polynomial_of_sdiff_iter_eventuallyZero
-- name    : GradedTransitivity.exists_polynomial_of_sdiff_iter_eventuallyZero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:09.426821+00:00
-- url     : https://prove2.me/theorems/3135c455-c856-46a9-b64a-1d972a8c9519
-- title:
--   From vanishing differences to a polynomial.
-- statement:
--   **From vanishing differences to a polynomial.**  If `Î^{r+1} a` vanishes
--   eventually then `a` eventually agrees with a polynomial of degree `â¤ r`.
--
--   ```lean
--   theorem GradedTransitivity.exists_polynomial_of_sdiff_iter_eventuallyZero{r : ℕ} {a : ℕ → ℚ}
--       (h : EventuallyZero (sdiff^[r + 1] a)) :
--       ∃ (N : ℕ) (p : ℚ[X]), p.natDegree ≤ r ∧ ∀ n ≥ N, a n = p.eval (n : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/PolyClassification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/PolyClassification.lean#L48

-- Thm stub generated from Shared/GradedTransitivity/PolyClassification.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolyClassification

/-!
# Denominator `(1-q)^{r+1}` ⟺ eventually polynomial of degree `≤ r`

`PolynomialGrowth` shows one implication and `Newton` produces, from the
vanishing of `Δ^{r+1}`, an explicit binomial expansion.  Here we convert that
binomial expansion into an honest polynomial, using the falling factorial
`descPochhammer`, and obtain the exact classification

`(1-q)^{r+1} · ∑ a n qⁿ` is a polynomial ⟺ `a` is eventually given by a
polynomial of degree `≤ r`.

## Main results

* `binomPoly_eval` : `C(n-N, j)` is a polynomial function of `n` of degree `j`.
* `exists_polynomial_of_sdiff_iter_eventuallyZero` : vanishing of `Δ^{r+1}`
  produces the polynomial.
* `gen_poly_iff_eventually_polynomial` : the classification.
-/

open GradedTransitivity

open Polynomial

theorem GradedTransitivity.exists_polynomial_of_sdiff_iter_eventuallyZero{r : ℕ} {a : ℕ → ℚ}
    (h : EventuallyZero (sdiff^[r + 1] a)) :
    ∃ (N : ℕ) (p : ℚ[X]), p.natDegree ≤ r ∧ ∀ n ≥ N, a n = p.eval (n : ℚ) := by sorry
