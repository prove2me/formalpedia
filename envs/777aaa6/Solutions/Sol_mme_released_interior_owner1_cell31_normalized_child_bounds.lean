-- Prove2me | solution 1 for mme_released_interior_owner1_cell31_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T11:48:04.994604+00:00
-- url     : https://prove2.me/submissions/65ea82e1-4726-45d8-bc4e-f1b6ce3670aa

import Theorems.Thm_mme_released_interior_owner1_cell31_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell31_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell31_region5_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner1_cell31_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell31_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner1_cell31_region5_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_zero_region_volume

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 31)
private def slot (c : ReleasedInterior.Split 31) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9190418775649264800000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 350583727916540469600000000000000000, 0, 0, 0, 3070385157244342173463722103607971504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17078964194638422640800000000000000000, 0, 0, 0, 19754823587415715517605283746598308424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1849944411051782191200000000000000000, 0, 0, 0, 350583727916540469600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1804174517966767200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69786292015848139200000000000000000, 0, 0, 0, 619786108323284876514795729542021878, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3301922816961600376800000000000000000, 0, 0, 0, 3817828509578924325651000025871510700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 373428670464088682400000000000000000, 0, 0, 0, 69786292015848139200000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3243751330184049600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125452344138400944000000000000000000, 0, 0, 0, 1110781885043868887724409336201409664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5913996545146878043200000000000000000, 0, 0, 0, 6838023412617679065267804186257600688, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 669259599316723641600000000000000000, 0, 0, 0, 125452344138400944000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 1 31).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 1 31 c.1 c.2 + ReleasedInterior.splitWeight 1 31 c.1
      (complement (ReleasedInterior.parent_total 31 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn2 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 968905719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36960511513, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1800560614999, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 195031560961, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36960511513, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b2 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℚ := (bn2 c z : ℚ) / 1000000000000
private def v2 (z : Fin 3) : ℚ := ((![36126520708154, 36077370863541, 36249635997232] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn3 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 190206241, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7357264026, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 348107303829, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39368954047, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7357264026, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b3 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℚ := (bn3 c z : ℚ) / 1000000000000
private def v3 (z : Fin 3) : ℚ := ((![36110212658532, 36077370863541, 36249635998894] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn5 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 341974538, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13225892820, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 623486830646, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70557117048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13225892820, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b5 (c : ReleasedInterior.Split 31) (z : Fin 3) : ℚ := (bn5 c z : ℚ) / 1000000000000
private def v5 (z : Fin 3) : ℚ := ((![36110214358079, 36077370863541, 36249635997864] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 31) → ℝ,
      (∑ c, q c) = (32752513985284344804713507564039411429 / 1000000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 31 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 1 31 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 1 31).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 1 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 1 31).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 1 31 c.1 c.2 + ReleasedInterior.splitWeight 1 31 c.1
            (complement (ReleasedInterior.parent_total 31 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (32752513985284344804713507564039411429 / 1000000000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hzero : (ReleasedInterior.seed 1 31).region.getD 0 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨0, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 31 ⟨0, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨0, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨0, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 1 31).region.getD 1 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨1, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 31 ⟨1, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨1, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨1, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3), (c.val z).val = 0 →
          q ⟨2, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b2 c z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b2 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region2_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn2 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3), (c.val z).val = 0 →
          q ⟨3, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b3 c z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b3 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region3_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn3 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hzero : (ReleasedInterior.seed 1 31).region.getD 4 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨4, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 1 31 ⟨4, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨4, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 1 31 (z + 1) ⟨4, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3), (c.val z).val = 0 →
          q ⟨5, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b5 c z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b5 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region5_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn5 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨0, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 31, theta ⟨0, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨1, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 31, theta ⟨1, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨2, c⟩ ≤ theta ⟨2, c⟩ * v2 z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * (v2 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region2_112_weight_rate_bound c z hz
      simp only [v2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨2, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨3, c⟩ ≤ theta ⟨3, c⟩ * v3 z := by decide +kernel
      have hqr : (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * (v3 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region3_112_weight_rate_bound c z hz
      simp only [v3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨3, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hqzero : ∀ c : ReleasedInterior.Split 31, q ⟨4, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 31, theta ⟨4, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hq : ∀ (c : ReleasedInterior.Split 31) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨5, c⟩ ≤ theta ⟨5, c⟩ * v5 z := by decide +kernel
      have hqr : (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * (v5 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner1_cell31_region5_112_weight_rate_bound c z hz
      simp only [v5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨5, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h


#print axioms solution
