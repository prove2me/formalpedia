-- Prove2me | solution 1 for mme_parent_mixture_rational_identity
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:23:34.943487+00:00
-- url     : https://prove2.me/submissions/b485ceb4-bcce-427e-aab3-13cd680b625f

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Tactic

open scoped BigOperators
open MME MME.RegionRealization MME.RecursiveYZ

/-- Parent mixtures computed from integer histograms agree exactly with
rational arithmetic, including zero parent masses and zero child rows. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal n m mu r w =
      (((∑ c, (m r c : ℚ) *
        ((mu ⟨r, c⟩ (w 0) : ℚ) / (∑ v, mu ⟨r, c⟩ v : ℕ)) *
        ((mu ⟨r, complement (htotal r) c⟩ (w 1) : ℚ) /
          (∑ v, mu ⟨r, complement (htotal r) c⟩ v : ℕ))) / (n r : ℚ) : ℚ) : ℝ) := by
  simp only [parentMixture, cellFrequency, Rat.cast_div, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast]


#print axioms solution
