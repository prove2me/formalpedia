-- Prove2me | solution 1 for mme_regional_parent_compatibility_rational_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:43.570981+00:00
-- url     : https://prove2.me/submissions/d29571b8-ee97-49ee-8707-2399496fa49e

import Theorems.Thm_mme_parent_mixture_rational_identity
import Theorems.Thm_mme_rational_scaled_weighted_entropy_difference_certificate
import Definitions.Def_mme_regional_split_entropy_data

open scoped BigOperators Classical
open MME MME.RegionRate MME.RecursiveYZ

/-- Rational tables certified against the actual parent mixtures and
compatibility counts bound one complete directional regional rate. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (i : Fin 2)
    (scale : ℚ) (hscale : 0 ≤ scale)
    (weight : Fin R → ℚ) (hweight : ∀ r, 0 ≤ weight r)
    (hweightMatch : ∀ r, scale * weight r = (n r : ℚ))
    (p : Fin R → (Fin 2 → W) → ℚ) (hp : ∀ r w, 0 ≤ p r w)
    (hpMatch : ∀ r w, p r w =
      (∑ c, (m r c : ℚ) *
        ((mu ⟨r, c⟩ (w 0) : ℚ) / (∑ v, mu ⟨r, c⟩ v : ℕ)) *
        ((mu ⟨r, complement (htotal r) c⟩ (w 1) : ℚ) /
          (∑ v, mu ⟨r, complement (htotal r) c⟩ v : ℕ))) / (n r : ℚ))
    (x : ({c : Cell half R parent // yzBoundary i c} ⊕
      (Fin R × Fin (half + 1))) → W → ℚ)
    (hx : ∀ c w, 0 ≤ x c w)
    (hxMatch : ∀ c w, scale * x c w =
      (partCount (yzBoundary i) (modeGroup (yzMode i)) mu c w : ℚ))
    (pLower pUpper : Fin R → (Fin 2 → W) → ℚ)
    (xLower xUpper : ({c : Cell half R parent // yzBoundary i c} ⊕
      (Fin R × Fin (half + 1))) → W → ℚ)
    (hpLog : ∀ r w, 0 < p r w →
      (pLower r w : ℝ) ≤ Real.log (p r w : ℝ) ∧
        Real.log (p r w : ℝ) ≤ (pUpper r w : ℝ))
    (hxLog : ∀ c w, 0 < x c w / ∑ v, x c v →
      (xLower c w : ℝ) ≤ Real.log ((x c w / ∑ v, x c v : ℚ) : ℝ) ∧
        Real.log ((x c w / ∑ v, x c v : ℚ) : ℝ) ≤ (xUpper c w : ℝ))
    (bound : ℚ)
    (hcert : bound ≤ (∑ r, weight r * (-(∑ w, p r w * pUpper r w))) -
      ∑ c, (∑ w, x c w) * (-(∑ w, (x c w / ∑ v, x c v) * xLower c w))) :
    (scale : ℝ) * (bound : ℝ) ≤
      parentPotential htotal n m mu - compatibilityPotential i mu := by
  have hpR (r : Fin R) : (fun w => (p r w : ℝ)) =
      RegionRealization.parentMixture htotal n m mu r := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hpMatch r w
  have hwR (r : Fin R) :
      (scale : ℝ) * (weight r : ℝ) = (n r : ℝ) := by
    exact_mod_cast hweightMatch r
  have hxR (c) (w : W) :
      (scale : ℝ) * (x c w : ℝ) =
        (partCount (yzBoundary i) (modeGroup (yzMode i)) mu c w : ℝ) := by
    exact_mod_cast hxMatch c w
  have h := mme_rational_scaled_weighted_entropy_difference_certificate weight hweight
    p hp x hx pLower pUpper xLower xUpper hpLog hxLog
    (scale : ℝ) (by exact_mod_cast hscale) bound hcert
  simp_rw [hwR, hpR, hxR] at h
  rw [compatibilityPotential,
    (mme_regional_mass_entropy_algebra (C := _) (W := W)).2.2]
  exact h


#print axioms solution
