-- Prove2me | solution 1 for mme_certified_entropy_rational_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T21:01:24.434569+00:00
-- url     : https://prove2.me/submissions/9702c3a4-db5c-448a-a49a-099ab1cddb03

import Mathlib
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_auto_scaled_log_interval_data
import Theorems.Thm_mme_certified_entropy_bounds
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
open BigOperators MME MME.RegionRate MME.Cert Finset
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
universe u

namespace MME.Cert

variable {W : Type u} [Fintype W]

/-- The log part of a certificate, as a combination of the four prime logarithms. -/
theorem log_part (p : W → ℚ) (e : W → Fin 4 → ℤ) (A : Fin 4 → ℚ)
    (hA : ∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j) :
    ∑ w, ((p w : ℚ) : ℝ) * Real.log (qval (e w)) =
      ∑ j, ((A j : ℚ) : ℝ) * Real.log (primeOf j) := by
  have hstep : ∀ w, ((p w : ℚ) : ℝ) * Real.log (qval (e w)) =
      ∑ j, ((p w : ℚ) : ℝ) * ((e w j : ℤ) : ℝ) * Real.log (primeOf j) := by
    intro w
    rw [log_qval_prime (e w), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [Finset.sum_congr rfl (fun w _ ↦ hstep w), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_mul, ← hA j]
  push_cast
  ring

/-- Termwise interval bound on a signed multiple of a logarithm. -/
theorem signed_le (a : ℚ) (L : ℝ) (lo hi : ℚ) (hlo : (lo : ℝ) ≤ L) (hhi : L ≤ (hi : ℝ)) :
    (a : ℝ) * L ≤ ((if 0 ≤ a then a * hi else a * lo : ℚ) : ℝ) := by
  by_cases h : 0 ≤ a
  · rw [if_pos h]
    push_cast
    exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast h)
  · rw [if_neg h]
    push_cast
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := le_of_lt (lt_of_not_ge h)
      exact_mod_cast this
    nlinarith [hlo]

theorem signed_ge (a : ℚ) (L : ℝ) (lo hi : ℚ) (hlo : (lo : ℝ) ≤ L) (hhi : L ≤ (hi : ℝ)) :
    ((if 0 ≤ a then a * lo else a * hi : ℚ) : ℝ) ≤ (a : ℝ) * L := by
  by_cases h : 0 ≤ a
  · rw [if_pos h]
    push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast h)
  · rw [if_neg h]
    push_cast
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := le_of_lt (lt_of_not_ge h)
      exact_mod_cast this
    nlinarith [hhi]

/-- A rational floor for the entropy of a rational distribution, from a reference table and
certified enclosures of the four prime logarithms. -/
theorem entropy_floor (p : W → ℚ) (hp : ∀ w, 0 ≤ p w) (e : W → Fin 4 → ℤ)
    (R : ℚ) (A : Fin 4 → ℚ) (lo hi : Fin 4 → ℚ)
    (hR : ∑ w, (p w - (p w) ^ 2 / qvalQ (e w)) = R)
    (hA : ∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j)
    (hlo : ∀ j, ((lo j : ℚ) : ℝ) ≤ Real.log (primeOf j))
    (hhi : ∀ j, Real.log (primeOf j) ≤ ((hi j : ℚ) : ℝ)) :
    ((R - ∑ j, (if 0 ≤ A j then A j * hi j else A j * lo j) : ℚ) : ℝ) ≤
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) := by
  have hge := mme_certified_entropy_bounds.1 (fun w ↦ ((p w : ℚ) : ℝ)) (fun w ↦ by show (0:ℝ) ≤ ((p w : ℚ) : ℝ); exact_mod_cast hp w) e
  have hsplit : ∑ w, (((p w : ℚ) : ℝ) - ((p w : ℚ) : ℝ) ^ 2 / qval (e w) -
      ((p w : ℚ) : ℝ) * Real.log (qval (e w))) =
      ((R : ℚ) : ℝ) - ∑ j, ((A j : ℚ) : ℝ) * Real.log (primeOf j) := by
    rw [Finset.sum_sub_distrib, log_part p e A hA]
    congr 1
    rw [← hR]
    push_cast
    exact Finset.sum_congr rfl (fun w _ ↦ by rw [qvalQ_cast (e w)])
  rw [hsplit] at hge
  refine le_trans ?_ hge
  have hterm : ∑ j, ((A j : ℚ) : ℝ) * Real.log (primeOf j) ≤
      ((∑ j, (if 0 ≤ A j then A j * hi j else A j * lo j) : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun j _ ↦ signed_le (A j) _ (lo j) (hi j) (hlo j) (hhi j))
  push_cast
  push_cast at hterm
  linarith

/-- A rational ceiling for the entropy of a rational distribution. -/
theorem entropy_ceil (p : W → ℚ) (hp : ∀ w, 0 ≤ p w) (e : W → Fin 4 → ℤ)
    (S : ℚ) (A : Fin 4 → ℚ) (lo hi : Fin 4 → ℚ)
    (hS : ∑ w, (qvalQ (e w) - p w) = S)
    (hA : ∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j)
    (hlo : ∀ j, ((lo j : ℚ) : ℝ) ≤ Real.log (primeOf j))
    (hhi : ∀ j, Real.log (primeOf j) ≤ ((hi j : ℚ) : ℝ)) :
    entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤
      ((S - ∑ j, (if 0 ≤ A j then A j * lo j else A j * hi j) : ℚ) : ℝ) := by
  have hle := mme_certified_entropy_bounds.2.1 (fun w ↦ ((p w : ℚ) : ℝ)) (fun w ↦ by show (0:ℝ) ≤ ((p w : ℚ) : ℝ); exact_mod_cast hp w) e
  have hsplit : ∑ w, (qval (e w) - ((p w : ℚ) : ℝ) -
      ((p w : ℚ) : ℝ) * Real.log (qval (e w))) =
      ((S : ℚ) : ℝ) - ∑ j, ((A j : ℚ) : ℝ) * Real.log (primeOf j) := by
    rw [Finset.sum_sub_distrib, log_part p e A hA]
    congr 1
    rw [← hS]
    push_cast
    exact Finset.sum_congr rfl (fun w _ ↦ by rw [qvalQ_cast (e w)])
  rw [hsplit] at hle
  refine le_trans hle ?_
  have hterm : ((∑ j, (if 0 ≤ A j then A j * lo j else A j * hi j) : ℚ) : ℝ) ≤
      ∑ j, ((A j : ℚ) : ℝ) * Real.log (primeOf j) := by
    push_cast
    exact Finset.sum_le_sum (fun j _ ↦ signed_ge (A j) _ (lo j) (hi j) (hlo j) (hhi j))
  push_cast
  push_cast at hterm
  linarith

theorem logInterval2 :
    ((693147180559945309417232/10^24 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) ∧
      Real.log ((2 : ℕ) : ℝ) ≤ ((693147180559945309417233/10^24 : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := mme_log_interval_of_auto_scaled_rational (2 : ℚ) 0 30 (by norm_num) (by norm_num)
  have hq : (((2 : ℚ)) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hq] at hl hu
  have hlo : ((693147180559945309417232/10^24 : ℚ)) ≤ autoScaledLogLower (2 : ℚ) 0 30 := by
    norm_num [autoScaledLogLower, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  have hhi : autoScaledLogUpper (2 : ℚ) 0 30 ≤ ((693147180559945309417233/10^24 : ℚ)) := by
    norm_num [autoScaledLogUpper, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  exact ⟨le_trans (by exact_mod_cast hlo) hl, le_trans hu (by exact_mod_cast hhi)⟩

theorem logInterval3 :
    ((1098612288668109691395245/10^24 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ) : ℝ) ∧
      Real.log ((3 : ℕ) : ℝ) ≤ ((1098612288668109691395246/10^24 : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := mme_log_interval_of_auto_scaled_rational (3 : ℚ) 0 45 (by norm_num) (by norm_num)
  have hq : (((3 : ℚ)) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [hq] at hl hu
  have hlo : ((1098612288668109691395245/10^24 : ℚ)) ≤ autoScaledLogLower (3 : ℚ) 0 45 := by
    norm_num [autoScaledLogLower, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  have hhi : autoScaledLogUpper (3 : ℚ) 0 45 ≤ ((1098612288668109691395246/10^24 : ℚ)) := by
    norm_num [autoScaledLogUpper, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  exact ⟨le_trans (by exact_mod_cast hlo) hl, le_trans hu (by exact_mod_cast hhi)⟩

theorem logInterval5 :
    ((1609437912434100374600759/10^24 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ) : ℝ) ∧
      Real.log ((5 : ℕ) : ℝ) ≤ ((1609437912434100374600760/10^24 : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := mme_log_interval_of_auto_scaled_rational (5 : ℚ) 0 80 (by norm_num) (by norm_num)
  have hq : (((5 : ℚ)) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  rw [hq] at hl hu
  have hlo : ((1609437912434100374600759/10^24 : ℚ)) ≤ autoScaledLogLower (5 : ℚ) 0 80 := by
    norm_num [autoScaledLogLower, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  have hhi : autoScaledLogUpper (5 : ℚ) 0 80 ≤ ((1609437912434100374600760/10^24 : ℚ)) := by
    norm_num [autoScaledLogUpper, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  exact ⟨le_trans (by exact_mod_cast hlo) hl, le_trans hu (by exact_mod_cast hhi)⟩

theorem logInterval7 :
    ((1945910149055313305105352/10^24 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ) : ℝ) ∧
      Real.log ((7 : ℕ) : ℝ) ≤ ((1945910149055313305105353/10^24 : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := mme_log_interval_of_auto_scaled_rational (7 : ℚ) 0 110 (by norm_num) (by norm_num)
  have hq : (((7 : ℚ)) : ℝ) = ((7 : ℕ) : ℝ) := by norm_num
  rw [hq] at hl hu
  have hlo : ((1945910149055313305105352/10^24 : ℚ)) ≤ autoScaledLogLower (7 : ℚ) 0 110 := by
    norm_num [autoScaledLogLower, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  have hhi : autoScaledLogUpper (7 : ℚ) 0 110 ≤ ((1945910149055313305105353/10^24 : ℚ)) := by
    norm_num [autoScaledLogUpper, autoScaledLogPartial, autoScaledLogParameter,
      Finset.sum_range_succ]
  exact ⟨le_trans (by exact_mod_cast hlo) hl, le_trans hu (by exact_mod_cast hhi)⟩

theorem logLo_le (j : Fin 4) : ((logLo j : ℚ) : ℝ) ≤ Real.log (primeOf j) := by
  match j with
  | 0 => exact logInterval2.1
  | 1 => exact logInterval3.1
  | 2 => exact logInterval5.1
  | 3 => exact logInterval7.1

theorem logHi_ge (j : Fin 4) : Real.log (primeOf j) ≤ ((logHi j : ℚ) : ℝ) := by
  match j with
  | 0 => exact logInterval2.2
  | 1 => exact logInterval3.2
  | 2 => exact logInterval5.2
  | 3 => exact logInterval7.2

end MME.Cert

theorem solution :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ (e : W → Fin 4 → ℤ)
      (R : ℚ) (A : Fin 4 → ℚ),
      ∑ w, (p w - (p w) ^ 2 / qvalQ (e w)) = R →
      (∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j) →
      ((R - ∑ j, (if 0 ≤ A j then A j * logHi j else A j * logLo j) : ℚ) : ℝ) ≤
        entropy (fun w ↦ ((p w : ℚ) : ℝ))) ∧
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ (e : W → Fin 4 → ℤ)
      (S : ℚ) (A : Fin 4 → ℚ),
      ∑ w, (qvalQ (e w) - p w) = S →
      (∀ j, ∑ w, p w * ((e w j : ℤ) : ℚ) = A j) →
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤
        ((S - ∑ j, (if 0 ≤ A j then A j * logLo j else A j * logHi j) : ℚ) : ℝ)) ∧
    (∀ j : Fin 4, ((logLo j : ℚ) : ℝ) ≤ Real.log (primeOf j)) ∧
    ∀ j : Fin 4, Real.log (primeOf j) ≤ ((logHi j : ℚ) : ℝ) :=
  ⟨fun {W} _ p hp e R A hR hA ↦
      MME.Cert.entropy_floor p hp e R A logLo logHi hR hA MME.Cert.logLo_le MME.Cert.logHi_ge,
   fun {W} _ p hp e S A hS hA ↦
      MME.Cert.entropy_ceil p hp e S A logLo logHi hS hA MME.Cert.logLo_le MME.Cert.logHi_ge,
   MME.Cert.logLo_le, MME.Cert.logHi_ge⟩
