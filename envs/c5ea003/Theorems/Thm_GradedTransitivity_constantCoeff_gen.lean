-- Prove2me | Theorems.Thm_GradedTransitivity_constantCoeff_gen
-- name    : GradedTransitivity.constantCoeff_gen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:37:26.98098+00:00
-- url     : https://prove2.me/theorems/bd4b302c-79d4-4026-b409-a3ca0ea33074
-- title:
--   ConstantCoeff gen
-- statement:
--   Formal statement of `GradedTransitivity.constantCoeff_gen` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GradedTransitivity.constantCoeff_gen(a : ℕ → ℚ) :
--       (PowerSeries.constantCoeff) (gen a) = a 0 := by sorry
--   /-! ### Eventually zero sequences are exactly the polynomials -/
--
--
--
--   /-! ### The key power series identity -/
--
--
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/FiniteDifference.lean#L42

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





@[simp]

theorem GradedTransitivity.constantCoeff_gen(a : ℕ → ℚ) :
    (PowerSeries.constantCoeff) (gen a) = a 0 := by sorry
