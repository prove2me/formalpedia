-- Prove2me | solution 1 for StereographicCapacityContrarian.s2_cap_packing_area_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:10:54.449256+00:00
-- url     : https://prove2.me/submissions/b493bd11-9c5b-4871-8f68-9a94deacf3ac

-- Sol generated from Geometry/StereographicCapacity/Contrarian.lean
import Mathlib
import Definitions.Def_Geometry_StereographicCapacity_Contrarian
import Theorems.Thm_StereographicCapacityContrarian_finite_disjoint_packing

/-!
# Contrarian results for stereographic capacity on `S²`

This self-contained file separates the area argument from the proposed stereographic
correction and tests the claimed calibrations.  Caps of geodesic radius `r` have
area `2π(1-cos r)`.  Pairwise disjoint caps therefore satisfy the stronger direct
area bound `card ≤ 2/(1-cos r)`.

The proposed correction `(2/cos r)^2` does not tend to one: at `r = 0` it equals
four.  Moreover, four caps of radius `π/3` cannot be packed.  Their centers would
be unit vectors with every mutual inner product at most `cos(2π/3) = -1/2`, which
contradicts nonnegativity of the squared norm of their sum.  Thus the advertised
"tetrahedral" calibration is false for caps of that radius.
-/

open scoped ENNReal
open MeasureTheory Set Finset Real

open StereographicCapacityContrarian

noncomputable section














open StereographicCapacityContrarian in
theorem solution    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (caps : ι → Set α) (ambient : Set α)
    (r : ℝ) (hr : 0 < r) (hrpi : r < Real.pi)
    (hmeas : ∀ i ∈ s, MeasurableSet (caps i))
    (hsub : ∀ i ∈ s, caps i ⊆ ambient)
    (hdisj : Set.PairwiseDisjoint (s : Set ι) caps)
    (hsphere : μ ambient = ENNReal.ofReal sphereArea)
    (hcaps : ∀ i ∈ s, μ (caps i) = ENNReal.ofReal (capArea r)) :
    (s.card : ℝ) ≤ 2 / (1 - Real.cos r) := by
  have hcap_pos : 0 < capArea r := by
    simp [capArea]
    apply mul_pos (mul_pos two_pos Real.pi_pos)
    have hc : Real.cos r < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : (0 : ℝ) ≤ 0) (by linarith : r ≤ Real.pi) hr
    exact sub_pos.mpr hc
  have hpacking := finite_disjoint_packing μ s caps ambient hmeas hsub hdisj _ (fun i hi => le_of_eq (hcaps i hi).symm)
  rw [hsphere] at hpacking
  have hsphere_nonneg : 0 ≤ sphereArea := by simp [sphereArea]; exact Real.pi_pos.le
  have hpacked_real : (s.card : ℝ) * capArea r ≤ sphereArea := by
    have h1 : ((s.card : ℕ) * ENNReal.ofReal (capArea r)).toReal ≤ (ENNReal.ofReal sphereArea).toReal := by
      apply ENNReal.toReal_mono
      · exact ne_of_lt (ENNReal.ofReal_lt_top)
      · exact hpacking
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (le_of_lt hcap_pos),
         ENNReal.toReal_ofReal hsphere_nonneg] at h1
  simp [capArea, sphereArea] at hpacked_real
  rw [le_div_iff₀ (sub_pos.mpr (by rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : (0 : ℝ) ≤ 0) (by linarith : r ≤ Real.pi) hr))]
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith [sq_nonneg Real.pi]
