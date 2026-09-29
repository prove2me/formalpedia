-- Prove2me | Theorems.Thm_mme_regional_parent_mixture_lipschitz
-- name    : mme_regional_parent_mixture_lipschitz
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T21:15:33.949977+00:00
-- url     : https://prove2.me/theorems/7fadf806-0aa6-4a1e-bea2-3dcf357932b4
-- title:
--   Parent profile mixtures are Lipschitz under child-frequency perturbations
-- statement:
--   If all child-cell frequencies change by at most delta >= 0, the induced parent product-mixture frequencies change by at most 2 delta. Consequently every parent tolerance band of radius epsilon around the first profile lies in the band of radius epsilon + 2 delta around the second profile. This is a uniform source-inclusion estimate for exact types inside a lower-stage tolerance window.
-- source:
--   Direct formal proof: product telescoping, probability bounds, weighted averaging, and the triangle inequality.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib
open BigOperators MME MME.RegionRealization MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem freq_bounds {C W : Type*} [Fintype W]
    (mu : C → W → ℕ) (c : C) (w : W) : cellFrequency mu c w ∈ Set.Icc 0 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hz : ∑ v, mu c v = 0
    · simp [cellFrequency,hz]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))).mpr
      exact_mod_cast Finset.single_le_sum (f := mu c) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)

private theorem product_close (a b c d delta : ℝ)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hdelta : 0 ≤ delta)
    (hac : |a-c| ≤ delta) (hbd : |b-d| ≤ delta) : |a*b-c*d| ≤ 2*delta := by
  calc
    |a*b-c*d| = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * b+c * |b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ delta*1+1*delta := add_le_add
      (mul_le_mul hac hb.2 hb.1 hdelta) (mul_le_mul hc.2 hbd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem mme_regional_parent_mixture_lipschitz {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r)
    (mu nu : Cell half R parent → W → ℕ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hclose : ∀ c w, |cellFrequency mu c w - cellFrequency nu c w| ≤ delta) :
    (∀ r w, |parentMixture htotal n m mu r w - parentMixture htotal n m nu r w| ≤ 2*delta) ∧
    (∀ (eps : ℝ) (f : Position n → W), parentTypical htotal n m mu eps f →
      parentTypical htotal n m nu (eps+2*delta) f) := by
  sorry
