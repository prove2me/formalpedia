-- Prove2me | solution 1 for mme_regional_parent_compatibility_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:03:58.578873+00:00
-- url     : https://prove2.me/submissions/e5b1b308-6c28-466f-9862-1709c590b598

import Theorems.Thm_mme_regional_compatibility_potential_sum

open scoped BigOperators Classical
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ

/-- Uniform normalized regional margins yield the weighted global
parent-minus-compatibility bound. Empty regions have zero profiles. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (i : Fin 2) (b : ℝ)
    (hzero : ∀ r, n r = 0 → ∀ c w, mu ⟨r, c⟩ w = 0)
    (hb : ∀ r, 0 < n r → b ≤ entropy (parentMixture htotal n m mu r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ) / n r)) :
    b * (∑ r, n r : ℕ) ≤ parentPotential htotal n m mu - compatibilityPotential i mu := by
  have hregion (r : Fin R) : b * (n r : ℝ) ≤
      (n r : ℝ) * entropy (parentMixture htotal n m mu r) -
        ∑ t, massEntropy (fun w =>
          (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
            (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) := by
    by_cases hz : n r = 0
    · simp [hz, partCount, hzero r hz, massEntropy, entropy]
    · have hnR : (n r : ℝ) ≠ 0 := by exact_mod_cast hz
      have he (t) : massEntropy (fun w =>
          (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
            (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) =
          (n r : ℝ) * massEntropy (fun w =>
          (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
            (fun c w => mu ⟨r, c⟩ w) t w : ℝ) / n r) := by
        rw [← (mme_regional_mass_entropy_algebra (C := Unit)).1]
        congr 1
        funext w
        field_simp
      have h := mul_le_mul_of_nonneg_left (hb r (Nat.pos_of_ne_zero hz))
        (Nat.cast_nonneg (n r) : (0 : ℝ) ≤ n r)
      simpa only [mul_sub, Finset.mul_sum, ← he, mul_comm b] using h
  rw [parentPotential, mme_regional_compatibility_potential_sum]
  simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_sub_distrib] using
    Finset.sum_le_sum (fun r _ => hregion r)


#print axioms solution
