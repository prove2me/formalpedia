-- Prove2me | solution 1 for mme_certified_potential_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:09:09.525047+00:00
-- url     : https://prove2.me/submissions/e231cb48-f4dc-44bf-94e8-0790e35c3f7c

import Mathlib
import Definitions.Def_mme_certified_generic_ceiling_data
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_region_count_entropy_data
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v


namespace MME.Cert

theorem regCeilG_ge {W : Type u} [Fintype W] (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (e : W → Fin 4 → ℤ) :
    entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤ ((regCeilG p e : ℚ) : ℝ) :=
  mme_certified_entropy_rational_floor.2.1 p hp e _ _ rfl (fun _ ↦ rfl)

/-- A certified rational ceiling for a compatibility-style potential. -/
theorem potential_ceilG {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ)
    (e : C → W → Fin 4 → ℤ) (g : C → ℚ)
    (hg : ∀ c, regCeilG (freqQ mu c) (e c) ≤ g c) :
    RegionRealization.potential mu ≤ ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * ((g c : ℚ) : ℝ) := by
  rw [mme_certified_entropy_bridge.{u, v}.2.1 mu]
  refine Finset.sum_le_sum (fun c _ ↦ ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (regCeilG_ge (freqQ mu c)
    (fun w ↦ (mme_certified_entropy_bridge.{u, v}.1 mu c w).1) (e c)) ?_
  exact_mod_cast hg c


end MME.Cert

theorem solution :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤ ((regCeilG p e : ℚ) : ℝ)) ∧
    ∀ {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ)
      (e : C → W → Fin 4 → ℤ) (g : C → ℚ),
      (∀ c, regCeilG (freqQ mu c) (e c) ≤ g c) →
      RegionRealization.potential mu ≤ ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * ((g c : ℚ) : ℝ) :=
  ⟨fun {W} _ p hp e ↦ MME.Cert.regCeilG_ge p hp e,
   fun {C} {W} _ _ mu e g hg ↦ MME.Cert.potential_ceilG mu e g hg⟩
