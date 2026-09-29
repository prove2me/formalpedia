-- Prove2me | solution 1 for mme_certified_point_mass_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:36:23.506606+00:00
-- url     : https://prove2.me/submissions/dd7372b6-72c3-436f-8afa-744497951006

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v


namespace MME.Cert

/-- A distribution concentrated on one letter has zero entropy. -/
theorem entropy_point {W : Type u} [Fintype W] (p : W → ℚ) (w0 : W)
    (h : ∀ w, p w = if w = w0 then 1 else 0) :
    entropy (fun w ↦ ((p w : ℚ) : ℝ)) = 0 := by
  classical
  show ∑ w, Real.negMulLog ((p w : ℚ) : ℝ) = 0
  refine Finset.sum_eq_zero (fun w _ ↦ ?_)
  rw [h w]
  by_cases hw : w = w0
  · rw [if_pos hw]
    norm_num [Real.negMulLog]
  · rw [if_neg hw]
    norm_num [Real.negMulLog]

/-- A profile supported on one word contributes nothing to a potential. -/
theorem freqQ_point {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w0 : W)
    (hz : ∀ w, w ≠ w0 → mu c w = 0) (hp : mu c w0 ≠ 0) :
    entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ)) = 0 := by
  classical
  have htot : (∑ v, mu c v) = mu c w0 := by
    refine Finset.sum_eq_single w0 (fun v _ hv ↦ hz v hv) (fun h ↦ absurd (Finset.mem_univ _) h)
  refine entropy_point (fun w ↦ freqQ mu c w) w0 (fun w ↦ ?_)
  unfold freqQ
  rw [htot]
  by_cases hw : w = w0
  · rw [if_pos hw, hw]
    exact div_self (by exact_mod_cast hp)
  · rw [if_neg hw]
    show ((mu c w : ℚ)) / ((mu c w0 : ℕ) : ℚ) = 0
    rw [hz w hw]
    norm_num


end MME.Cert

theorem solution :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ) (w0 : W),
      (∀ w, p w = if w = w0 then 1 else 0) →
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) = 0) ∧
    ∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w0 : W),
      (∀ w, w ≠ w0 → mu c w = 0) → mu c w0 ≠ 0 →
      entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ)) = 0 :=
  ⟨fun {W} _ p w0 h ↦ MME.Cert.entropy_point p w0 h,
   fun {C} {W} _ mu c w0 hz hp ↦ MME.Cert.freqQ_point mu c w0 hz hp⟩
