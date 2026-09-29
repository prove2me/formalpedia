-- Prove2me | solution 1 for flt7_dvd_7a6_nat
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:52:12.030265+00:00
-- url     : https://prove2.me/submissions/f019a63b-a724-4fac-a0c8-fe41e89d5080

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

private def phi7_wit (a b : ℤ) : ℤ :=
  (a:ℤ)^6 - (a:ℤ)^5*b + (a:ℤ)^4*b^2 - (a:ℤ)^3*b^3 + (a:ℤ)^2*b^4 - a*b^5 + b^6

private lemma apb_dvd_sum7_int (a b : ℕ) :
    ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) := by
  have h : (a:ℤ)+b ∣ (a:ℤ)^7+b^7 := ⟨phi7_wit a b, by unfold phi7_wit; ring⟩
  have h2 : ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) := by push_cast; exact h
  exact h2

private lemma apb_mul_phi7_nat (a b : ℕ) :
    (a+b) * ((a^7+b^7)/(a+b)) = a^7+b^7 :=
  Nat.mul_div_cancel' (by exact_mod_cast apb_dvd_sum7_int a b)

private lemma phi7_nat_eq_int (a b : ℕ) (hab_ne : a+b ≠ 0) :
    (((a^7+b^7)/(a+b):ℕ):ℤ) = phi7_wit a b := by
  have hprod := apb_mul_phi7_nat a b
  have hab_ne_int : (a:ℤ)+b ≠ 0 := by exact_mod_cast hab_ne
  apply mul_left_cancel₀ hab_ne_int
  have h1 : ((a:ℤ)+b) * (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^7+b^7 := by
    have : (((a+b) * ((a^7+b^7)/(a+b)):ℕ):ℤ) = ((a^7+b^7:ℕ):ℤ) := by exact_mod_cast hprod
    push_cast at this ⊢; linarith
  rw [h1]; unfold phi7_wit; ring

theorem solution (a b q : ℕ) (hab_ne : a+b ≠ 0)
    (hqab : q ∣ a+b) (hqphi : q ∣ (a^7+b^7)/(a+b)) : q ∣ 7*a^6 := by
  have heq : (((a^7+b^7)/(a+b):ℕ):ℤ) = phi7_wit a b := phi7_nat_eq_int a b hab_ne
  have hq_int : (q:ℤ) ∣ 7*(a:ℤ)^6 := by
    have hqab_int : (q:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hqab
    have hqphi_int : (q:ℤ) ∣ phi7_wit a b := heq ▸ (by exact_mod_cast hqphi)
    have hident : (a:ℤ)+b ∣ phi7_wit a b - 7*(a:ℤ)^6 :=
      ⟨-6*(a:ℤ)^5+5*(a:ℤ)^4*b-4*(a:ℤ)^3*b^2+3*(a:ℤ)^2*b^3-2*(a:ℤ)*b^4+b^5,
       by unfold phi7_wit; ring⟩
    have h1 : (q:ℤ) ∣ phi7_wit a b - 7*(a:ℤ)^6 := dvd_trans hqab_int hident
    have h2 := dvd_sub hqphi_int h1
    convert h2 using 1; ring
  exact_mod_cast hq_int
