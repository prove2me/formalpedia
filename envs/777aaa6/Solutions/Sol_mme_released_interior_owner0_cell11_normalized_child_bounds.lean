-- Prove2me | solution 1 for mme_released_interior_owner0_cell11_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T06:20:34.827984+00:00
-- url     : https://prove2.me/submissions/3206069f-a1af-443c-9a63-6563cf0e6bc1

import Theorems.Thm_mme_released_interior_owner0_cell11_region0_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell11_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell11_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell11_region0_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner0_cell11_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner0_cell11_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_zero_region_volume

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 11)
private def slot (c : ReleasedInterior.Split 11) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 5628768068751361912800000000000000000, 0, 0, 0, 4342027654851366175200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3036243125999094660000000000000000000, 0, 0, 0, 9297769264698423118632468073594280370, 0, 0, 0, 191888980279681127425964832272340690, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5009662514389301992800000000000000000, 0, 0, 0, 3850124013052031952000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2692291535814431534400000000000000000, 0, 0, 0, 8275111993217280922017260810469186336, 0, 0, 0, 171244717872767593417273435250570500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3374617368189454300800000000000000000, 0, 0, 0, 2589637509006828717600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1810751761762292246400000000000000000, 0, 0, 0, 5574294990105160329768171709413657819, 0, 0, 0, 115715317255634581088111228006382222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 0 11).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 0 11 c.1 c.2 + ReleasedInterior.splitWeight 0 11 c.1
      (complement (ReleasedInterior.parent_total 11 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn0 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 593416437909, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 457761014981, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 320097854175, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b0 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℚ := (bn0 c z : ℚ) / 1000000000000
private def v0 (z : Fin 3) : ℚ := ((![36077370863541, 36249640610698, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn2 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 528146842809, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 405901762060, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 283836539982, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b2 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℚ := (bn2 c z : ℚ) / 1000000000000
private def v2 (z : Fin 3) : ℚ := ((![36077370863541, 36249640610455, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn3 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 355771172924, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 273014174203, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 190899651092, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b3 (c : ReleasedInterior.Split 11) (z : Fin 3) : ℚ := (bn3 c z : ℚ) / 1000000000000
private def v3 (z : Fin 3) : ℚ := ((![36077370863541, 36249640609462, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 11) → ℝ,
      (∑ c, q c) = (55960148815245111164349250089006417937 / 2000000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 11 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 0 11 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 0 11).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 0 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 0 11).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 0 11 c.1 c.2 + ReleasedInterior.splitWeight 0 11 c.1
            (complement (ReleasedInterior.parent_total 11 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (55960148815245111164349250089006417937 / 2000000000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3), (c.val z).val = 0 →
          q ⟨0, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b0 c z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b0 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region0_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn0 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hzero : (ReleasedInterior.seed 0 11).region.getD 1 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨1, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 11 ⟨1, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨1, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨1, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3), (c.val z).val = 0 →
          q ⟨2, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b2 c z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b2 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region2_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn2 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3), (c.val z).val = 0 →
          q ⟨3, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b3 c z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b3 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region3_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn3 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hzero : (ReleasedInterior.seed 0 11).region.getD 4 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨4, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 11 ⟨4, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨4, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨4, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 0 11).region.getD 5 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨5, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 11 ⟨5, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨5, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 11 (z + 1) ⟨5, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨0, c⟩ ≤ theta ⟨0, c⟩ * v0 z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * (v0 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region0_112_weight_rate_bound c z hz
      simp only [v0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨0, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨1, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 11, theta ⟨1, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨2, c⟩ ≤ theta ⟨2, c⟩ * v2 z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * (v2 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region2_112_weight_rate_bound c z hz
      simp only [v2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨2, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 11) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨3, c⟩ ≤ theta ⟨3, c⟩ * v3 z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * (v3 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell11_region3_112_weight_rate_bound c z hz
      simp only [v3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨3, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨4, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 11, theta ⟨4, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 11, q ⟨5, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 11, theta ⟨5, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _


#print axioms solution
