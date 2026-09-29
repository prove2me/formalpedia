-- Prove2me | Theorems.Thm_GradedTransitivity_binomial_generating_function
-- name    : GradedTransitivity.binomial_generating_function
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:03.236984+00:00
-- url     : https://prove2.me/theorems/e151a224-a8e0-4cd8-85af-294b0d43894d
-- title:
--   The binomial generating function.
-- statement:
--   **The binomial generating function.**  In `PowerSeries â`,
--   `(1 - X)^{r+1} Â· â_n C(n,r) Xâ¿ = X^r`, i.e. `â_n C(n,r) qâ¿ = q^r/(1-q)^{r+1}`.
--
--   ```lean
--   theorem GradedTransitivity.binomial_generating_function(r : ℕ) :
--       (1 - PowerSeries.X) ^ (r + 1) * gen (chooseSeq r) = (PowerSeries.X : PowerSeries ℚ) ^ r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/BinomialGF.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/BinomialGF.lean#L52

-- Thm stub generated from Shared/GradedTransitivity/BinomialGF.lean
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

theorem GradedTransitivity.binomial_generating_function(r : ℕ) :
    (1 - PowerSeries.X) ^ (r + 1) * gen (chooseSeq r) = (PowerSeries.X : PowerSeries ℚ) ^ r := by sorry
