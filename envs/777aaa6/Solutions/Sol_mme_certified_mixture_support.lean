-- Prove2me | solution 1 for mme_certified_mixture_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:29:25.432194+00:00
-- url     : https://prove2.me/submissions/2644cccd-4f53-4d3a-b1c1-b56d9b11c338

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v


namespace MME.Cert

variable {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}

/-- A cell frequency vanishes where its profile does. -/
theorem freqQ_zero {C : Type v} (mu : C → W → ℕ) (c : C) (w : W) (h : mu c w = 0) :
    freqQ mu c w = 0 := by
  unfold freqQ
  rw [h]
  norm_num

/-- A parent mixture vanishes at any word pair that no split can produce. -/
theorem mixQ_zero
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W)
    (h : ∀ c, mu ⟨r, c⟩ (w 0) = 0 ∨ mu ⟨r, complement (htotal r) c⟩ (w 1) = 0) :
    mixQ htotal n m mu r w = 0 := by
  unfold mixQ
  rw [show (∑ c, (m r c : ℚ) * freqQ mu ⟨r, c⟩ (w 0) *
      freqQ mu ⟨r, complement (htotal r) c⟩ (w 1)) = 0 from ?_]
  · norm_num
  · refine Finset.sum_eq_zero (fun c _ ↦ ?_)
    rcases h c with hc | hc
    · rw [freqQ_zero mu ⟨r, c⟩ (w 0) hc]
      ring
    · rw [freqQ_zero mu ⟨r, complement (htotal r) c⟩ (w 1) hc]
      ring


end MME.Cert

theorem solution :
    (∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W),
      mu c w = 0 → freqQ mu c w = 0) ∧
    ∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W),
      (∀ c, mu ⟨r, c⟩ (w 0) = 0 ∨ mu ⟨r, complement (htotal r) c⟩ (w 1) = 0) →
      mixQ htotal n m mu r w = 0 :=
  ⟨fun {C} {W} _ mu c w h ↦ MME.Cert.freqQ_zero mu c w h,
   fun {half} {R} {W} _ {parent} htotal n m mu r w h ↦
     MME.Cert.mixQ_zero htotal n m mu r w h⟩
