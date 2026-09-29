-- Prove2me | solution 1 for mme_certified_entropy_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T21:12:42.041483+00:00
-- url     : https://prove2.me/submissions/ef7ef16f-d9fa-47ae-8f58-87f91529ab6c

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_region_count_entropy_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_certified_entropy_bounds
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

namespace MME.Cert

theorem log_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'

/-- Entropy in nats is the bit entropy scaled by `log 2`. -/
theorem entropyBits_mul {W : Type u} [Fintype W] (p : W → ℝ) :
    Real.log 2 * mme_modern_entropyBits p = entropy p := by
  unfold mme_modern_entropyBits entropy
  field_simp

theorem freqQ_nonneg {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W) :
    0 ≤ freqQ mu c w := by
  unfold freqQ
  positivity

theorem freqQ_cast {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W) :
    cellFrequency mu c w = ((freqQ mu c w : ℚ) : ℝ) := by
  unfold cellFrequency freqQ
  push_cast
  ring

/-- The compatibility-style potential, as a weighted sum of rational entropies. -/
theorem potential_eq {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ) :
    RegionRealization.potential mu =
      ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ)) := by
  unfold RegionRealization.potential
  refine Finset.sum_congr rfl (fun c _ ↦ ?_)
  rw [mul_assoc, entropyBits_mul]
  exact congrArg (fun z ↦ ((∑ w, mu c w : ℕ) : ℝ) * z)
    (congrArg entropy (funext fun w ↦ freqQ_cast mu c w))

variable {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}

theorem mixQ_nonneg (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W) :
    0 ≤ mixQ htotal n m mu r w := by
  unfold mixQ
  refine div_nonneg (Finset.sum_nonneg (fun c _ ↦ ?_)) (by positivity)
  exact mul_nonneg (mul_nonneg (by positivity) (freqQ_nonneg mu _ _)) (freqQ_nonneg mu _ _)

theorem mixQ_cast (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal n m mu r w = ((mixQ htotal n m mu r w : ℚ) : ℝ) := by
  unfold parentMixture mixQ
  rw [Rat.cast_div]
  have hnum : ∑ c, (m r c : ℝ) * cellFrequency mu ⟨r, c⟩ (w 0) *
      cellFrequency mu ⟨r, complement (htotal r) c⟩ (w 1) =
      ((∑ c, (m r c : ℚ) * freqQ mu ⟨r, c⟩ (w 0) *
        freqQ mu ⟨r, complement (htotal r) c⟩ (w 1) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun c _ ↦ ?_)
    rw [freqQ_cast mu ⟨r, c⟩ (w 0), freqQ_cast mu ⟨r, complement (htotal r) c⟩ (w 1)]
  rw [hnum]
  norm_num

/-- The parent potential, as a weighted sum of rational entropies. -/
theorem parentPotential_eq (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) :
    parentPotential htotal n m mu =
      ∑ r, ((n r : ℕ) : ℝ) * entropy (fun w ↦ ((mixQ htotal n m mu r w : ℚ) : ℝ)) := by
  unfold parentPotential
  refine Finset.sum_congr rfl (fun r _ ↦ ?_)
  exact congrArg (fun z ↦ ((n r : ℕ) : ℝ) * z)
    (congrArg entropy (funext fun w ↦ mixQ_cast htotal n m mu r w))

theorem normQ_nonneg {W : Type u} [Fintype W] (x : W → ℕ) (w : W) : 0 ≤ normQ x w := by
  unfold normQ
  positivity

/-- Unnormalized entropy of natural masses, as a rational-distribution entropy. -/
theorem massEntropy_natQ {W : Type u} [Fintype W] (x : W → ℕ) (h : 0 < ∑ w, x w) :
    massEntropy (fun w ↦ ((x w : ℕ) : ℝ)) =
      ((∑ w, x w : ℕ) : ℝ) * entropy (fun w ↦ ((normQ x w : ℚ) : ℝ)) := by
  have hS : (0 : ℝ) < ∑ w, ((x w : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((∑ w, x w : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_sum] at this
  rw [mme_certified_entropy_bounds.2.2 (fun w ↦ ((x w : ℕ) : ℝ)) hS]
  rw [Nat.cast_sum]
  refine congrArg (fun z ↦ (∑ w, ((x w : ℕ) : ℝ)) * z) (congrArg entropy (funext fun w ↦ ?_))
  unfold normQ
  push_cast
  rfl

/-- The coarse potential, as a weighted sum of rational entropies. -/
theorem coarsePotential_eq {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3)
    (hpos : ∀ r, 0 < ∑ j, marginalCounts m i r j) :
    coarsePotential m i =
      ∑ r, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) *
        entropy (fun j ↦ ((normQ (marginalCounts m i r) j : ℚ) : ℝ)) := by
  unfold coarsePotential
  exact Finset.sum_congr rfl (fun r _ ↦ massEntropy_natQ (marginalCounts m i r) (hpos r))

end MME.Cert

theorem solution :
    (∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W),
      0 ≤ freqQ mu c w ∧ cellFrequency mu c w = ((freqQ mu c w : ℚ) : ℝ)) ∧
    (∀ {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ),
      RegionRealization.potential mu =
        ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ))) ∧
    (∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W),
      0 ≤ mixQ htotal n m mu r w ∧
        parentMixture htotal n m mu r w = ((mixQ htotal n m mu r w : ℚ) : ℝ)) ∧
    (∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ),
      parentPotential htotal n m mu =
        ∑ r, ((n r : ℕ) : ℝ) * entropy (fun w ↦ ((mixQ htotal n m mu r w : ℚ) : ℝ))) ∧
    (∀ {W : Type u} [Fintype W] (x : W → ℕ) (w : W), 0 ≤ normQ x w) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3),
      (∀ r, 0 < ∑ j, marginalCounts m i r j) →
      coarsePotential m i =
        ∑ r, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts m i r) j : ℚ) : ℝ)) :=
  ⟨fun {C} {W} _ mu c w ↦ ⟨MME.Cert.freqQ_nonneg mu c w, MME.Cert.freqQ_cast mu c w⟩,
   fun {C} {W} _ _ mu ↦ MME.Cert.potential_eq mu,
   fun {half} {R} {W} _ {parent} htotal n m mu r w ↦
     ⟨MME.Cert.mixQ_nonneg htotal n m mu r w, MME.Cert.mixQ_cast htotal n m mu r w⟩,
   fun {half} {R} {W} _ {parent} htotal n m mu ↦ MME.Cert.parentPotential_eq htotal n m mu,
   fun {W} _ x w ↦ MME.Cert.normQ_nonneg x w,
   fun {half} {R} {parent} m i hpos ↦ MME.Cert.coarsePotential_eq m i hpos⟩
