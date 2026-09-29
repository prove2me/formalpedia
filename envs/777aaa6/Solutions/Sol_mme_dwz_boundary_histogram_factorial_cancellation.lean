-- Prove2me | solution 1 for mme_dwz_boundary_histogram_factorial_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:40:59.66095+00:00
-- url     : https://prove2.me/submissions/f936ea85-c28b-41ea-8514-b718c14df60b

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring

open BigOperators

set_option autoImplicit false

namespace MME.DWZJoint

theorem prod_div_mul_prod_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (h : ∀ i, b i ∣ a i) :
    (∏ i, a i / b i) * (∏ i, b i) = ∏ i, a i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ ↦ Nat.div_mul_cancel (h i))

theorem compatible_count_cancellation
    (R Q T D BB BP G F CB CP BD RD P : ℕ)
    (hR : R * (BD * RD) = F) (hQ : Q * CP = P)
    (hT : T * F = G) (hD : D * (CB * CP) = G)
    (hBB : BB * BD = CB) (hBP : BP * RD = P)
    (hden : BD * RD * CP ≠ 0) :
    (R * Q) * T = D * (BB * BP) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hden)
  calc
    (R * Q * T) * (BD * RD * CP) = (R * (BD * RD)) * (Q * CP) * T := by ring
    _ = F * P * T := by rw [hR, hQ]
    _ = (T * F) * P := by ring
    _ = G * P := by rw [hT]
    _ = (D * (CB * CP)) * P := by rw [hD]
    _ = (D * ((BB * BD) * CP)) * (BP * RD) := by rw [hBB, hBP]
    _ = (D * (BB * BP)) * (BD * RD * CP) := by ring

theorem boundary_histogram_factorial_cancellation
    {B P L : Type*} [Fintype B] [Fintype P] [Fintype L]
    (b : B → L → ℕ) (r gamma : L → ℕ) (p : P → ℕ)
    (hcolumn : ∀ l, gamma l = r l + ∑ c, b c l)
    (hpositive : ∑ l, r l = ∑ c, p c) :
    ((∏ l, (gamma l).factorial /
      ((r l).factorial * ∏ c, (b c l).factorial)) *
      ((∑ l, r l).factorial / ∏ c, (p c).factorial)) *
      ((∑ l, gamma l).factorial / ∏ l, (gamma l).factorial) =
    ((∑ l, gamma l).factorial /
      ((∏ c, (∑ l, b c l).factorial) * ∏ c, (p c).factorial)) *
      ((∏ c, (∑ l, b c l).factorial / ∏ l, (b c l).factorial) *
        ((∑ l, r l).factorial / ∏ l, (r l).factorial)) := by
  classical
  have hdR (l : L) :
      (r l).factorial * (∏ c, (b c l).factorial) ∣ (gamma l).factorial := by
    rw [hcolumn l]
    exact (Nat.mul_dvd_mul_left _ (Nat.prod_factorial_dvd_factorial_sum
      (s := Finset.univ) (f := fun c ↦ b c l))).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hR := prod_div_mul_prod_eq (fun l ↦ (gamma l).factorial)
    (fun l ↦ (r l).factorial * ∏ c, (b c l).factorial) hdR
  have hR' : (∏ l, (gamma l).factorial /
      ((r l).factorial * ∏ c, (b c l).factorial)) *
      ((∏ c, ∏ l, (b c l).factorial) * ∏ l, (r l).factorial) =
        ∏ l, (gamma l).factorial := by
    have hswap : (∏ l, ∏ c, (b c l).factorial) =
        ∏ c, ∏ l, (b c l).factorial := Finset.prod_comm
    rw [Finset.prod_mul_distrib, hswap,
      mul_comm (∏ l, (r l).factorial)] at hR
    exact hR
  have hQ : ((∑ l, r l).factorial / ∏ c, (p c).factorial) *
      (∏ c, (p c).factorial) = (∑ l, r l).factorial := by
    apply Nat.div_mul_cancel
    rw [hpositive]
    exact Nat.prod_factorial_dvd_factorial_sum _ _
  have hT : ((∑ l, gamma l).factorial / ∏ l, (gamma l).factorial) *
      (∏ l, (gamma l).factorial) = (∑ l, gamma l).factorial :=
    Nat.div_mul_cancel (Nat.prod_factorial_dvd_factorial_sum _ _)
  have htotal : (∑ l, gamma l) = (∑ c, ∑ l, b c l) + ∑ c, p c := by
    simp_rw [hcolumn]
    rw [Finset.sum_add_distrib, hpositive, Finset.sum_comm]
    omega
  have hD : ((∑ l, gamma l).factorial /
      ((∏ c, (∑ l, b c l).factorial) * ∏ c, (p c).factorial)) *
      ((∏ c, (∑ l, b c l).factorial) * ∏ c, (p c).factorial) =
        (∑ l, gamma l).factorial := by
    apply Nat.div_mul_cancel
    rw [htotal]
    exact (Nat.mul_dvd_mul
      (Nat.prod_factorial_dvd_factorial_sum (s := Finset.univ) (f := fun c ↦ ∑ l, b c l))
      (Nat.prod_factorial_dvd_factorial_sum (s := Finset.univ) (f := p))).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hBB : (∏ c, (∑ l, b c l).factorial / ∏ l, (b c l).factorial) *
      (∏ c, ∏ l, (b c l).factorial) = ∏ c, (∑ l, b c l).factorial :=
    prod_div_mul_prod_eq _ _ (fun c ↦ Nat.prod_factorial_dvd_factorial_sum _ _)
  have hBP : ((∑ l, r l).factorial / ∏ l, (r l).factorial) *
      (∏ l, (r l).factorial) = (∑ l, r l).factorial :=
    Nat.div_mul_cancel (Nat.prod_factorial_dvd_factorial_sum _ _)
  have hden : (∏ c, ∏ l, (b c l).factorial) *
      (∏ l, (r l).factorial) * (∏ c, (p c).factorial) ≠ 0 := by
    positivity
  exact compatible_count_cancellation _ _ _ _ _ _ _ _ _ _ _ _ _
    hR' hQ hT hD hBB hBP hden

theorem boundary_histogram_factorial_cancellation_product
    {K L : Type*} {B P : K → Type*}
    [Fintype K] [Fintype L] [∀ k, Fintype (B k)] [∀ k, Fintype (P k)]
    (b : ∀ k, B k → L → ℕ) (r gamma : K → L → ℕ) (p : ∀ k, P k → ℕ)
    (hcolumn : ∀ k l, gamma k l = r k l + ∑ c, b k c l)
    (hpositive : ∀ k, (∑ l, r k l) = ∑ c, p k c) :
    ((∏ k, ∏ l, (gamma k l).factorial /
      ((r k l).factorial * ∏ c, (b k c l).factorial)) *
      (∏ k, (∑ l, r k l).factorial / ∏ c, (p k c).factorial)) *
      (∏ k, (∑ l, gamma k l).factorial / ∏ l, (gamma k l).factorial) =
    (∏ k, (∑ l, gamma k l).factorial /
      ((∏ c, (∑ l, b k c l).factorial) * ∏ c, (p k c).factorial)) *
      ((∏ k, ∏ c, (∑ l, b k c l).factorial / ∏ l, (b k c l).factorial) *
        (∏ k, (∑ l, r k l).factorial / ∏ l, (r k l).factorial)) := by
  classical
  have hprod := congrArg (fun f : K → ℕ ↦ ∏ k, f k)
    (funext (fun k ↦ boundary_histogram_factorial_cancellation
      (b k) (r k) (gamma k) (p k) (hcolumn k) (hpositive k)))
  simpa only [Finset.prod_mul_distrib] using hprod

end MME.DWZJoint

theorem solution
    {K L : Type*} {B P : K → Type*}
    [Fintype K] [Fintype L] [∀ k, Fintype (B k)] [∀ k, Fintype (P k)]
    (b : ∀ k, B k → L → ℕ) (r gamma : K → L → ℕ) (p : ∀ k, P k → ℕ)
    (hcolumn : ∀ k l, gamma k l = r k l + ∑ c, b k c l)
    (hpositive : ∀ k, (∑ l, r k l) = ∑ c, p k c) :
    ((∏ k, ∏ l, (gamma k l).factorial /
      ((r k l).factorial * ∏ c, (b k c l).factorial)) *
      (∏ k, (∑ l, r k l).factorial / ∏ c, (p k c).factorial)) *
      (∏ k, (∑ l, gamma k l).factorial / ∏ l, (gamma k l).factorial) =
    (∏ k, (∑ l, gamma k l).factorial /
      ((∏ c, (∑ l, b k c l).factorial) * ∏ c, (p k c).factorial)) *
      ((∏ k, ∏ c, (∑ l, b k c l).factorial / ∏ l, (b k c l).factorial) *
        (∏ k, (∑ l, r k l).factorial / ∏ l, (r k l).factorial)) := by
  exact MME.DWZJoint.boundary_histogram_factorial_cancellation_product
    b r gamma p hcolumn hpositive

