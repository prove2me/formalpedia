-- Prove2me | solution 1 for mme_certified_parent_potential_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:03:38.126898+00:00
-- url     : https://prove2.me/submissions/9d05be3f-7035-4c7b-8879-52bcb6c778ab

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u


namespace MME.Cert

theorem regFloorG_le {W : Type u} [Fintype W] (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (e : W → Fin 4 → ℤ) :
    ((regFloorG p e : ℚ) : ℝ) ≤ entropy (fun w ↦ ((p w : ℚ) : ℝ)) :=
  mme_certified_entropy_rational_floor.1 p hp e _ _ rfl (fun _ ↦ rfl)

variable {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}

/-- A certified rational floor for any parent potential, from per-region reference tables. -/
theorem parentPotential_floorG
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (e : Fin R → (Fin 2 → W) → Fin 4 → ℤ) (f : Fin R → ℚ)
    (hf : ∀ r, f r ≤ regFloorG (mixQ htotal n m mu r) (e r)) :
    (∑ r : Fin R, ((n r : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤ parentPotential htotal n m mu := by
  rw [mme_certified_entropy_bridge.{u, u}.2.2.2.1 htotal n m mu]
  refine Finset.sum_le_sum (fun r _ ↦ ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (regFloorG_le (mixQ htotal n m mu r)
    (fun w ↦ (mme_certified_entropy_bridge.{u, u}.2.2.1 htotal n m mu r w).1) (e r))
  exact_mod_cast hf r


end MME.Cert

theorem solution :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      ((regFloorG p e : ℚ) : ℝ) ≤ entropy (fun w ↦ ((p w : ℚ) : ℝ))) ∧
    ∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ)
      (e : Fin R → (Fin 2 → W) → Fin 4 → ℤ) (f : Fin R → ℚ),
      (∀ r, f r ≤ regFloorG (mixQ htotal n m mu r) (e r)) →
      (∑ r : Fin R, ((n r : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤ parentPotential htotal n m mu :=
  ⟨fun {W} _ p hp e ↦ MME.Cert.regFloorG_le p hp e,
   fun {half} {R} {W} _ {parent} htotal n m mu e f hf ↦
     MME.Cert.parentPotential_floorG htotal n m mu e f hf⟩
