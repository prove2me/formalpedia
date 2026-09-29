-- Prove2me | solution 1 for GradedTransitivity.exists_poly_pow_mul_gen
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:15.087815+00:00
-- url     : https://prove2.me/submissions/db72163a-94b9-420b-9a9e-6f383fc83813

-- Sol generated from Shared/GradedTransitivity/FiniteDifference.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Theorems.Thm_GradedTransitivity_coeff_gen
import Theorems.Thm_GradedTransitivity_one_sub_X_mul_gen

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

/-- A sequence which vanishes eventually has a polynomial generating series. -/
theorem exists_poly_of_eventuallyZero {a : ℕ → ℚ} (h : EventuallyZero a) :
    ∃ p : ℚ[X], (p : PowerSeries ℚ) = gen a := by
  obtain ⟨N, hN⟩ := h
  refine ⟨∑ i ∈ Finset.range N, C (a i) * X ^ i, ?_⟩
  ext n
  rw [Polynomial.coeff_coe, coeff_gen]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq (Finset.range N) n]
  by_cases hn : n < N
  · simp [Finset.mem_range.2 hn]
  · simp only [Finset.mem_range, hn, if_false]
    exact (hN n (not_lt.1 hn)).symm


/-! ### The key power series identity -/


/-! ### Rationality: the forward direction -/


/-! ### Rationality: the converse -/




/-! ### Reformulation as an honest quotient of power series -/



open GradedTransitivity in
theorem solution:
    ∀ (k : ℕ) (a : ℕ → ℚ), EventuallyZero (sdiff^[k] a) →
      ∃ p : ℚ[X], (1 - PowerSeries.X) ^ k * gen a = (p : PowerSeries ℚ) := by
  intro k
  induction k with
  | zero =>
      intro a h
      simp only [Function.iterate_zero, id_eq] at h
      obtain ⟨p, hp⟩ := exists_poly_of_eventuallyZero h
      exact ⟨p, by simpa using hp.symm⟩
  | succ k ih =>
      intro a h
      rw [Function.iterate_succ_apply] at h
      obtain ⟨q, hq⟩ := ih (sdiff a) h
      refine ⟨X * q + (1 - X) ^ k * C (a 0), ?_⟩
      have : (1 - PowerSeries.X) ^ (k + 1) * gen a
          = (1 - PowerSeries.X) ^ k * ((1 - PowerSeries.X) * gen a) := by ring
      rw [this, one_sub_X_mul_gen, mul_add, ← mul_assoc, mul_comm ((1 - PowerSeries.X) ^ k)
        PowerSeries.X, mul_assoc, hq]
      push_cast
      ring
