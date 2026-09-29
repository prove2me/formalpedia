-- Prove2me | solution 1 for GradedTransitivity.eq_poly_div_of_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:13.528851+00:00
-- url     : https://prove2.me/submissions/073b0cd7-837d-43fb-aace-c01fa2944d6f

-- Sol generated from Shared/GradedTransitivity/FiniteDifference.lean
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


/-! ### Rationality: the forward direction -/


/-! ### Rationality: the converse -/




/-! ### Reformulation as an honest quotient of power series -/



open GradedTransitivity in
theorem solution{k : ℕ} {a : ℕ → ℚ} {p : ℚ[X]}
    (h : (1 - PowerSeries.X) ^ k * gen a = (p : PowerSeries ℚ)) :
    gen a = (p : PowerSeries ℚ) * (((1 - PowerSeries.X) ^ k)⁻¹ : PowerSeries ℚ) := by
  have hc : (PowerSeries.constantCoeff) ((1 - PowerSeries.X : PowerSeries ℚ) ^ k) ≠ 0 := by
    simp
  have hmul : ((1 - PowerSeries.X : PowerSeries ℚ) ^ k)
      * (((1 - PowerSeries.X : PowerSeries ℚ) ^ k)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ hc
  calc gen a = 1 * gen a := (one_mul _).symm
    _ = (((1 - PowerSeries.X : PowerSeries ℚ) ^ k)
          * (((1 - PowerSeries.X : PowerSeries ℚ) ^ k)⁻¹)) * gen a := by rw [hmul]
    _ = ((1 - PowerSeries.X : PowerSeries ℚ) ^ k * gen a)
          * (((1 - PowerSeries.X : PowerSeries ℚ) ^ k)⁻¹) := by ring
    _ = (p : PowerSeries ℚ) * (((1 - PowerSeries.X) ^ k)⁻¹ : PowerSeries ℚ) := by rw [h]
