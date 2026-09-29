-- Prove2me | Theorems.Thm_mme_regional_parent_compatibility_rational_certificate
-- name    : mme_regional_parent_compatibility_rational_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:08:48.857277+00:00
-- url     : https://prove2.me/theorems/c2c90467-a077-4347-af55-eb04931c42a7
-- title:
--   Rational tables certify actual directional parent-compatibility rates
-- statement:
--   Tables matched exactly to integer parent mixtures, parent masses, and compatibility class counts give a certified lower bound for the actual parent potential minus compatibility potential. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_parent_mixture_rational_identity
import Theorems.Thm_mme_rational_scaled_weighted_entropy_difference_certificate
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators Classical
open MME MME.RegionRate MME.RecursiveYZ

theorem mme_regional_parent_compatibility_rational_certificate
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
      parentPotential htotal n m mu - compatibilityPotential i mu := by sorry
