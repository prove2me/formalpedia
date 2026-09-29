-- Prove2me | solution 1 for GradedTransitivity.eventuallyZero_sdiff_iter_of_poly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:14.57503+00:00
-- url     : https://prove2.me/submissions/bb88d43e-eaf2-43d0-b03b-ddb28eb422de

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

/-- Conversely, a polynomial generating series forces the sequence to vanish
eventually. -/
theorem eventuallyZero_of_poly {a : ℕ → ℚ} {p : ℚ[X]}
    (h : (p : PowerSeries ℚ) = gen a) : EventuallyZero a := by
  refine ⟨p.natDegree + 1, fun n hn => ?_⟩
  have := congrArg (fun φ => (PowerSeries.coeff n) φ) h
  simp only [Polynomial.coeff_coe, coeff_gen] at this
  rw [← this]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ### The key power series identity -/


/-! ### Rationality: the forward direction -/


/-! ### Rationality: the converse -/

/-- If `X * φ` is a polynomial then so is `φ`. -/
theorem exists_poly_of_X_mul {φ : PowerSeries ℚ} {p : ℚ[X]}
    (h : PowerSeries.X * φ = (p : PowerSeries ℚ)) :
    ∃ q : ℚ[X], φ = (q : PowerSeries ℚ) := by
  have hz : EventuallyZero (fun n => (PowerSeries.coeff n) φ) := by
    refine ⟨p.natDegree + 1, fun n hn => ?_⟩
    have := congrArg (fun ψ => (PowerSeries.coeff (n + 1)) ψ) h
    simp only [PowerSeries.coeff_succ_X_mul, Polynomial.coeff_coe] at this
    show (PowerSeries.coeff n) φ = 0
    rw [this]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨q, hq⟩ := exists_poly_of_eventuallyZero hz
  exact ⟨q, by rw [hq]; ext n; simp⟩



/-! ### Reformulation as an honest quotient of power series -/



open GradedTransitivity in
theorem solution:
    ∀ (k : ℕ) (a : ℕ → ℚ) (p : ℚ[X]),
      (1 - PowerSeries.X) ^ k * gen a = (p : PowerSeries ℚ) →
        EventuallyZero (sdiff^[k] a) := by
  intro k
  induction k with
  | zero =>
      intro a p h
      simp only [pow_zero, one_mul] at h
      simpa using eventuallyZero_of_poly h.symm
  | succ k ih =>
      intro a p h
      rw [Function.iterate_succ_apply]
      have h1 : (1 - PowerSeries.X) ^ k * ((1 - PowerSeries.X) * gen a)
          = (p : PowerSeries ℚ) := by
        rw [← h]; ring
      rw [one_sub_X_mul_gen, mul_add] at h1
      have h2 : PowerSeries.X * ((1 - PowerSeries.X) ^ k * gen (sdiff a))
          = ((p - (1 - X) ^ k * C (a 0) : ℚ[X]) : PowerSeries ℚ) := by
        push_cast
        rw [← h1]
        ring
      obtain ⟨q, hq⟩ := exists_poly_of_X_mul h2
      exact ih (sdiff a) q hq
