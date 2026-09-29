-- Prove2me | Definitions.Def_Shared_GradedTransitivity_FiniteDifference
-- name    : Shared_GradedTransitivity_FiniteDifference
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:50:34.47733+00:00
-- url     : https://prove2.me/theorems/3a514d85-7480-424e-8ee2-a13df23a7bcb
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_FiniteDifference
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.FiniteDifference`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/FiniteDifference.lean by skeleton subtraction
import Mathlib

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

namespace GradedTransitivity

open Polynomial

/-- The forward difference operator on `ℚ`-valued sequences,
`(Δa)(n) = a (n+1) - a n`. -/
def sdiff (a : ℕ → ℚ) : ℕ → ℚ := fun n => a (n + 1) - a n

/-- A sequence is *eventually zero* if it vanishes from some index on. -/
def EventuallyZero (a : ℕ → ℚ) : Prop := ∃ N, ∀ n ≥ N, a n = 0

/-- The generating power series `∑ a n Xⁿ` of a sequence. -/
noncomputable def gen (a : ℕ → ℚ) : PowerSeries ℚ := PowerSeries.mk a



/-! ### Eventually zero sequences are exactly the polynomials -/



/-! ### The key power series identity -/


/-! ### Rationality: the forward direction -/


/-! ### Rationality: the converse -/




/-! ### Reformulation as an honest quotient of power series -/


end GradedTransitivity


