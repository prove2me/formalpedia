-- Prove2me | solution 1 for mme_regional_compatibility_component_sum
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:23:36.447068+00:00
-- url     : https://prove2.me/submissions/0d2285e8-9800-4452-a53c-440c1d04e97a

import Theorems.Thm_mme_partition_mass_entropy_full_sum
import Definitions.Def_mme_regional_split_entropy_data

open scoped BigOperators Classical
open MME.RegionRate MME.RegionRealization MME.RecursiveYZ

/-- A compatibility class retains its parent label, so its entropy can be
computed separately in each parent component before summing the region. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) :
    compatibilityPotential i mu = ∑ r : Fin R,
      ((∑ c : MME.RecursiveThinSplit.Split half (parent r),
          if yzBoundary i ⟨r, c⟩ then massEntropy (fun w ↦ (mu ⟨r, c⟩ w : ℝ)) else 0) +
       ∑ a : Fin (half + 1), massEntropy (fun w ↦
         ∑ c : MME.RecursiveThinSplit.Split half (parent r),
           if ¬ yzBoundary i ⟨r, c⟩ ∧ c.val (yzMode i) = a
           then (mu ⟨r, c⟩ w : ℝ) else 0)) := by
  classical
  unfold compatibilityPotential
  rw [mme_regional_mass_entropy_algebra.2.2]
  have h := mme_partition_mass_entropy_full_sum (yzBoundary i)
    (modeGroup (yzMode i)) mu 1
  simp only [Nat.cast_one, div_one] at h
  rw [h]
  simp only [Fintype.sum_sum_type]
  have hb (c : Cell half R parent) :
      massEntropy (fun w ↦ ((if yzBoundary i c then mu c w else 0 : ℕ) : ℝ)) =
        if yzBoundary i c then massEntropy (fun w ↦ (mu c w : ℝ)) else 0 := by
    by_cases hc : yzBoundary i c <;> simp [hc, massEntropy, entropy]
  simp_rw [hb]
  rw [Fintype.sum_sigma, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  funext w
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Fintype.sum_sigma,
    modeGroup, Prod.mk.injEq]
  have hf (s : Fin R) :
      (∑ c : MME.RecursiveThinSplit.Split half (parent s),
        if ¬ yzBoundary i ⟨s, c⟩ ∧ s = r ∧ c.val (yzMode i) = a
        then (mu ⟨s, c⟩ w : ℝ) else 0) =
      if hs : s = r then
        ∑ c : MME.RecursiveThinSplit.Split half (parent s),
          if ¬ yzBoundary i ⟨s, c⟩ ∧ c.val (yzMode i) = a
          then (mu ⟨s, c⟩ w : ℝ) else 0
      else 0 := by
    by_cases hs : s = r <;> simp [hs]
  simp_rw [hf]
  simp


#print axioms solution
