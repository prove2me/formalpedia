-- Prove2me | solution 1 for mme_released_interior_owner1_cell33_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T11:51:52.824418+00:00
-- url     : https://prove2.me/submissions/8c81eb45-53a7-4e5e-9c23-0f13a8c2238a

import Theorems.Thm_mme_released_interior_owner1_cell33_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell33_region4_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell33_region5_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell33_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell33_region4_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell33_region5_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_zero_region_volume

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 33)
private def slot (c : ReleasedInterior.Split 33) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3265963347588436800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1113120196712724360865701534564418440, 0, 0, 0, 126332724793116873600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6855693953346472721809761264963281400, 0, 0, 0, 5929252276327645147200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 126332724793116873600000000000000000, 0, 0, 0, 670668400710280058400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9186633292102214400000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3049771765895609907010057197899465340, 0, 0, 0, 350487926215461633600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19641740046182457175264679006597943408, 0, 0, 0, 16981145467325067175200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 350487926215461633600000000000000000, 0, 0, 0, 1837524428007997132800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1855393608001723200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 634768751589200137755866797782370344, 0, 0, 0, 71776338426646696800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3911529622928956921487451394368784044, 0, 0, 0, 3382946406471342592800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71776338426646696800000000000000000, 0, 0, 0, 382455861194773483200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 1 33).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 1 33 c.1 c.2 + ReleasedInterior.splitWeight 1 33 c.1
      (complement (ReleasedInterior.parent_total 33 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn3 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 344316254, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13318707508, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 625095175766, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13318707508, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70705640827, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b3 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℚ := (bn3 c z : ℚ) / 1000000000000
private def v3 (z : Fin 3) : ℚ := ((![36109959336954, 36249639232052, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn4 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 968506632, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36950411558, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1790248013731, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36950411558, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 193722176384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b4 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℚ := (bn4 c z : ℚ) / 1000000000000
private def v4 (z : Fin 3) : ℚ := ((![36126221150268, 36249639232122, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn5 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 195606046, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7567065929, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 356649267059, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7567065929, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40320651346, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b5 (c : ReleasedInterior.Split 33) (z : Fin 3) : ℚ := (bn5 c z : ℚ) / 1000000000000
private def v5 (z : Fin 3) : ℚ := ((![36109960657017, 36249639231929, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 33) → ℝ,
      (∑ c, q c) = (1023470611653291712440523706190254109 / 31250000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 33 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 1 33 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 1 33).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 1 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 1 33).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 1 33 c.1 c.2 + ReleasedInterior.splitWeight 1 33 c.1
            (complement (ReleasedInterior.parent_total 33 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (1023470611653291712440523706190254109 / 31250000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hzero : (ReleasedInterior.seed 1 33).region.getD 0 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨0, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 33 ⟨0, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨0, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨0, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 1 33).region.getD 1 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨1, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 33 ⟨1, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨1, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨1, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 1 33).region.getD 2 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨2, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 33 ⟨2, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨2, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 33 (z + 1) ⟨2, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3), (c.val z).val = 0 →
          q ⟨3, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b3 c z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b3 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region3_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn3 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3), (c.val z).val = 0 →
          q ⟨4, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b4 c z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b4 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region4_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn4 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3), (c.val z).val = 0 →
          q ⟨5, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b5 c z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b5 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region5_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn5 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨0, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 33, theta ⟨0, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨1, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 33, theta ⟨1, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 33, q ⟨2, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 33, theta ⟨2, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨3, c⟩ ≤ theta ⟨3, c⟩ * v3 z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * (v3 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region3_112_weight_rate_bound c z hz
      simp only [v3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨3, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨4, c⟩ ≤ theta ⟨4, c⟩ * v4 z := by decide +kernel
      have hqr : (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * (v4 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region4_112_weight_rate_bound c z hz
      simp only [v4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨4, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨5, c⟩ ≤ theta ⟨5, c⟩ * v5 z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * (v5 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell33_region5_112_weight_rate_bound c z hz
      simp only [v5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨5, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
