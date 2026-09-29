-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_eventuallyZero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:52:50.847097+00:00
-- url     : https://prove2.me/submissions/9610af5a-ff76-4492-819b-d5ed9a9852fb

-- Sol generated from Shared/GradedTransitivity/FiniteDifference.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Theorems.Thm_GradedTransitivity_eventuallyZero_sdiff_iter_of_poly
import Theorems.Thm_GradedTransitivity_exists_poly_pow_mul_gen

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
theorem solution(k : ℕ) (a : ℕ → ℚ) :
    (∃ p : ℚ[X], (1 - PowerSeries.X) ^ k * gen a = (p : PowerSeries ℚ)) ↔
      EventuallyZero (sdiff^[k] a) :=
  ⟨fun ⟨p, hp⟩ => eventuallyZero_sdiff_iter_of_poly k a p hp,
    exists_poly_pow_mul_gen k a⟩
