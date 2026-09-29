-- Prove2me | solution 1 for mme_regional_mass_entropy_algebra
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:02.063062+00:00
-- url     : https://prove2.me/submissions/bb240d3a-99ec-4a86-b4c3-9a6df42f1093

import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_region_count_entropy_data
import Mathlib

open BigOperators MME.RegionRate MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem homogeneous {W : Type*} [Fintype W] (a : ℝ) (x : W → ℝ) :
    massEntropy (fun w ↦ a * x w) = a * massEntropy x := by
  unfold massEntropy entropy
  rw [← Finset.mul_sum]
  simp only [Real.negMulLog_mul,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  ring

private theorem normalized {W : Type*} [Fintype W] (x : W → ℝ) (hs : ∑ w, x w ≠ 0) :
    massEntropy x = (∑ w, x w) * entropy (fun w ↦ x w / ∑ v, x v) := by
  have he : (∑ w, x w) * massEntropy (fun w ↦ x w / ∑ v, x v) = massEntropy x := by
    rw [← homogeneous]
    congr 1
    funext w
    field_simp
  have hn : (∑ w, x w / ∑ v, x v) = 1 := by rw [← Finset.sum_div]; exact div_self hs
  simpa only [massEntropy,hn,Real.negMulLog_one,sub_zero] using he.symm

theorem solution {C W : Type*} [Fintype C] [Fintype W] :
    (∀ (a : ℝ) (x : W → ℝ), massEntropy (fun w ↦ a * x w) = a * massEntropy x) ∧
    (∀ x : W → ℝ, (∑ w, x w) ≠ 0 →
      massEntropy x = (∑ w, x w) * entropy (fun w ↦ x w / ∑ v, x v)) ∧
    (∀ mu : C → W → ℕ, potential mu = ∑ c, massEntropy (fun w ↦ (mu c w : ℝ))) := by
  refine ⟨homogeneous,normalized,?_⟩
  intro mu
  unfold potential
  apply Finset.sum_congr rfl
  intro c hc
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  by_cases hz : ∑ w, mu c w = 0
  · have hw : ∀ w, mu c w = 0 := fun w ↦ Finset.sum_eq_zero_iff.mp hz w (Finset.mem_univ _)
    simp [hz,hw,massEntropy,entropy,mme_modern_entropyBits]
  · have hr : (∑ w, (mu c w : ℝ)) ≠ 0 := by exact_mod_cast hz
    rw [normalized _ hr]
    simp only [mme_modern_entropyBits,entropy,Nat.cast_sum]
    field_simp
