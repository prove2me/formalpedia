-- Prove2me | Theorems.Thm_GradedTransitivity_binomPoly_eval
-- name    : GradedTransitivity.binomPoly_eval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:12.709992+00:00
-- url     : https://prove2.me/theorems/36ba9e40-efde-4dc0-8ac0-b70553cf2929
-- title:
--   Past the shift, `binomPoly N j` computes the binomial coefficient.
-- statement:
--   Past the shift, `binomPoly N j` computes the binomial coefficient.
--
--   ```lean
--   theorem GradedTransitivity.binomPoly_eval(N j : ℕ) : ∀ n ≥ N, (binomPoly N j).eval (n : ℚ) = binomShift N j n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/PolyClassification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/PolyClassification.lean#L33

-- Thm stub generated from Shared/GradedTransitivity/PolyClassification.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_Newton
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

theorem GradedTransitivity.binomPoly_eval(N j : ℕ) : ∀ n ≥ N, (binomPoly N j).eval (n : ℚ) = binomShift N j n := by sorry
