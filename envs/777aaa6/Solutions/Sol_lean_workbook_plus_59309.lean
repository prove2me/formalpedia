-- Prove2me | solution 1 for lean_workbook_plus_59309
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:27:23.825184+00:00
-- url     : https://prove2.me/submissions/d965833f-bbc7-4614-8203-7ce4bd1f8f5d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open ComplexConjugate

theorem unit_triple_pair_sum (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hsum : a + b + c = 1) (hprod : a * b * c = 1) :
    a * b + b * c + c * a = 1 := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by rw [ha]; exact zero_lt_one)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (by rw [hb]; exact zero_lt_one)
  have hc0 : c ≠ 0 := norm_pos_iff.mp (by rw [hc]; exact zero_lt_one)
  have hi : a⁻¹ + b⁻¹ + c⁻¹ = 1 := by
    rw [Complex.inv_eq_conj ha, Complex.inv_eq_conj hb, Complex.inv_eq_conj hc]
    simpa only [map_add, map_one] using congrArg (starRingEnd ℂ) hsum
  have hm : (a * b * c) * (a⁻¹ + b⁻¹ + c⁻¹) = a * b + b * c + c * a := by
    field_simp [ha0, hb0, hc0]
    ring
  rw [hprod, hi, one_mul] at hm
  exact hm.symm

theorem unit_triple_factorization (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hsum : a + b + c = 1) (hprod : a * b * c = 1) (w : ℂ) :
    (w - a) * (w - b) * (w - c) =
      (w - 1) * (w - Complex.I) * (w + Complex.I) := by
  have hpair := unit_triple_pair_sum a b c ha hb hc hsum hprod
  calc
    (w - a) * (w - b) * (w - c) =
        w ^ 3 - (a + b + c) * w ^ 2 + (a * b + b * c + c * a) * w - a * b * c := by
          ring
    _ = w ^ 3 - w ^ 2 + w - 1 := by rw [hsum, hpair, hprod]; ring
    _ = (w - 1) * (w ^ 2 + 1) := by ring
    _ = (w - 1) * (w ^ 2 - Complex.I ^ 2) := by rw [Complex.I_sq]; ring
    _ = (w - 1) * (w - Complex.I) * (w + Complex.I) := by ring

theorem unit_triple_roots_iff (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hsum : a + b + c = 1) (hprod : a * b * c = 1) (w : ℂ) :
    (w = a ∨ w = b ∨ w = c) ↔ w = 1 ∨ w = Complex.I ∨ w = -Complex.I := by
  have hf : ((w - a) * (w - b) * (w - c) = 0) ↔
      (w - 1) * (w - Complex.I) * (w + Complex.I) = 0 := by
    rw [unit_triple_factorization a b c ha hb hc hsum hprod w]
  simpa only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hf

theorem cyclic_unit_ratios_classification (z₁ z₂ z₃ : ℂ)
    (h₀ : ‖z₁‖ = 1 ∧ ‖z₂‖ = 1 ∧ ‖z₃‖ = 1)
    (h₁ : z₁ / z₂ + z₂ / z₃ + z₃ / z₁ = 1) :
    z₁ / z₂ * z₂ / z₃ * z₃ / z₁ = 1 ∧
      ∀ w : ℂ, (w = z₁ / z₂ ∨ w = z₂ / z₃ ∨ w = z₃ / z₁) ↔
        w = 1 ∨ w = Complex.I ∨ w = -Complex.I := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp (by rw [h₀.1]; exact zero_lt_one)
  have hz₂ : z₂ ≠ 0 := norm_pos_iff.mp (by rw [h₀.2.1]; exact zero_lt_one)
  have hz₃ : z₃ ≠ 0 := norm_pos_iff.mp (by rw [h₀.2.2]; exact zero_lt_one)
  have ha : ‖z₁ / z₂‖ = 1 := by rw [norm_div, h₀.1, h₀.2.1, div_self one_ne_zero]
  have hb : ‖z₂ / z₃‖ = 1 := by rw [norm_div, h₀.2.1, h₀.2.2, div_self one_ne_zero]
  have hc : ‖z₃ / z₁‖ = 1 := by rw [norm_div, h₀.2.2, h₀.1, div_self one_ne_zero]
  have hp : (z₁ / z₂) * (z₂ / z₃) * (z₃ / z₁) = 1 := by
    field_simp [hz₁, hz₂, hz₃]
  refine ⟨?_, unit_triple_roots_iff _ _ _ ha hb hc h₁ hp⟩
  calc
    z₁ / z₂ * z₂ / z₃ * z₃ / z₁ = (z₁ / z₂) * (z₂ / z₃) * (z₃ / z₁) := by ring
    _ = 1 := hp

theorem solution (z₁ z₂ z₃ : ℂ)
    (h₀ : ‖z₁‖ = 1 ∧ ‖z₂‖ = 1 ∧ ‖z₃‖ = 1)
    (h₁ : z₁ / z₂ + z₂ / z₃ + z₃ / z₁ = 1) :
    z₁ / z₂ * z₂ / z₃ * z₃ / z₁ = 1 :=
  (cyclic_unit_ratios_classification z₁ z₂ z₃ h₀ h₁).1

#print axioms unit_triple_pair_sum
#print axioms unit_triple_factorization
#print axioms unit_triple_roots_iff
#print axioms cyclic_unit_ratios_classification
#print axioms solution
