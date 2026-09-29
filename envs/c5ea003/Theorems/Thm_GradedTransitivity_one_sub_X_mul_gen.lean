-- Prove2me | Theorems.Thm_GradedTransitivity_one_sub_X_mul_gen
-- name    : GradedTransitivity.one_sub_X_mul_gen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:23.550682+00:00
-- url     : https://prove2.me/theorems/7eddfddb-a0f8-44f0-b53c-9a6f49355c7b
-- title:
--   The fundamental identity relating multiplication by `1 - X` on generating
-- statement:
--   The fundamental identity relating multiplication by `1 - X` on generating
--   series with the forward difference operator on coefficients.
--
--   ```lean
--   theorem GradedTransitivity.one_sub_X_mul_gen(a : ℕ → ℚ) :
--       (1 - PowerSeries.X) * gen a
--         = PowerSeries.X * gen (sdiff a) + PowerSeries.C (a 0) := by sorry
--   /-! ### Rationality: the forward direction -/
--
--
--   /-! ### Rationality: the converse -/
--
--
--
--
--   /-! ### Reformulation as an honest quotient of power series -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/FiniteDifference.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/FiniteDifference.lean#L74

-- Thm stub generated from Shared/GradedTransitivity/FiniteDifference.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference

/-!
# Finite differences and rationality of generating functions

This file develops the analytic engine behind the main result of the
`Shared.GradedTransitivity` cluster:

> a sequence `a : ℕ → ℚ` has generating function `∑ a n qⁿ` equal to
> `P(q) / (1-q)^k` for a *polynomial* `P` **iff** the `k`-th forward
> difference of `a` vanishes eventually.

Everything is done inside `PowerSeries ℚ`, so no convergence issues arise; the
statement "`(1-q)^k` is a denominator" is formalised as
`(1 - X)^k * (∑ a n Xⁿ) = ↑P` for a polynomial `P`, which — since `1 - X` is a
unit of `PowerSeries ℚ` — is equivalent to `∑ a n Xⁿ = ↑P * ((1-X)^k)⁻¹`
(see `PowerSeries.eq_poly_div_of_pow_mul`).

## Main results

* `sdiff_iter_eventuallyZero_iff` : the iff above.
* `exists_poly_of_eventually_polynomial` : if `a` agrees eventually with a
  polynomial of degree `≤ r`, the denominator `(1-q)^{r+1}` suffices.
-/

open GradedTransitivity

open Polynomial






/-! ### Eventually zero sequences are exactly the polynomials -/



/-! ### The key power series identity -/

theorem GradedTransitivity.one_sub_X_mul_gen(a : ℕ → ℚ) :
    (1 - PowerSeries.X) * gen a
      = PowerSeries.X * gen (sdiff a) + PowerSeries.C (a 0) := by sorry
