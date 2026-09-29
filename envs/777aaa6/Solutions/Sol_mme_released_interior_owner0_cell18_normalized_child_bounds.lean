-- Prove2me | solution 1 for mme_released_interior_owner0_cell18_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T07:00:31.290329+00:00
-- url     : https://prove2.me/submissions/69ca4386-50d0-4f87-bd3c-76f220208722

import Theorems.Thm_mme_released_interior_owner0_cell18_region0_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell18_region1_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell18_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner0_cell18_region0_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner0_cell18_region1_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner0_cell18_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_zero_region_volume

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

private abbrev Child := Cell 4 6 (ReleasedInterior.parent 18)
private def slot (c : ReleasedInterior.Split 18) : ℕ := 25 * (c.val 0).val + 5 * (c.val 1).val + (c.val 2).val
private def q (c : Child) : ℚ :=
  (([0, 0, 0, 0, 0, 0, 0, 0, 2691652446373460421600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5009309707260113524800000000000000000, 0, 0, 0, 8274529215744193995459939230270170968, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3849203499548494687200000000000000000, 0, 0, 0, 171169825865964338746828397504375568, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1816115753931142989600000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3385121375062868400000000000000000000, 0, 0, 0, 5591645826205462229077271787636816000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2597304678349756651200000000000000000, 0, 0, 0, 116019227578080532122660328848140000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3030689538250980264000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5619523448906908473600000000000000000, 0, 0, 0, 9282498722152732522547158358316153768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4334078132146260547200000000000000000, 0, 0, 0, 191530678688133350207770888639380666, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (125 * c.1.val + slot c.2) 0 : ℚ) / 2000000000000000000000000000000000000
private def theta (c : Child) : ℚ :=
  ((ReleasedInterior.seed 0 18).region.getD c.1.val 0 : ℚ) / denominator *
    ((ReleasedInterior.splitWeight 0 18 c.1 c.2 + ReleasedInterior.splitWeight 0 18 c.1
      (complement (ReleasedInterior.parent_total 18 c.1) c.2) : ℕ) : ℚ) / denominator / 2
private def bn0 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 283769163573, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 528109647894, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 405804716341, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b0 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℚ := (bn0 c z : ℚ) / 1000000000000
private def v0 (z : Fin 3) : ℚ := ((![36249640627022, 36077370863541, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn1 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191465153363, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 356878564500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 273822490386, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b1 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℚ := (bn1 c z : ℚ) / 1000000000000
private def v1 (z : Fin 3) : ℚ := ((![36249640627004, 36077370863541, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000
private def bn2 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 319512363670, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 592441818008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 456922931516, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (3 * slot c + z.val) 0
private def b2 (c : ReleasedInterior.Split 18) (z : Fin 3) : ℚ := (bn2 c z : ℚ) / 1000000000000
private def v2 (z : Fin 3) : ℚ := ((![36249640627023, 36077370863541, 36077370863541] : Fin 3 → ℕ) z : ℚ) / 1000000000000

/-- One complete released parent has a certified normalized child table,
valid for every boundary free mode and every interior grade-two mode. -/
theorem solution :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 18) → ℝ,
      (∑ c, q c) = (5596039207606455292736162899121503697 / 200000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 18 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 0 18 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 0 18).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 0 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 0 18).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 0 18 c.1 c.2 + ReleasedInterior.splitWeight 0 18 c.1
            (complement (ReleasedInterior.parent_total 18 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  refine ⟨fun c ↦ (q c : ℝ), ?_, ?_, ?_⟩
  · have hs : (∑ c, q c) = (5596039207606455292736162899121503697 / 200000000000000000000000000000000000 : ℚ) := by decide +kernel
    have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hsR
  · rintro ⟨r, c⟩ z hz
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3), (c.val z).val = 0 →
          q ⟨0, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b0 c z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b0 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region0_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn0 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3), (c.val z).val = 0 →
          q ⟨1, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b1 c z := by decide +kernel
      have hqr : (q ⟨1, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b1 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region1_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn1 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3), (c.val z).val = 0 →
          q ⟨2, c⟩ ≤ 6 * (3952233 / 5000000 : ℚ) * b2 c z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) * (b2 c z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region2_boundary_volume_bound c z hz
      change (denominator : ℝ) ^ 4 * ((bn2 c z : ℝ) / 1000000000000) ≤ _ at hv
      simp only [b2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have h1 := mul_le_mul_of_nonneg_left hqr (show 0 ≤ (denominator : ℝ) ^ 4 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6 * (3952233 / 5000000 : ℝ) by norm_num)
      apply h1.trans
      convert h2 using 1; ring
    · have hzero : (ReleasedInterior.seed 0 18).region.getD 3 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨3, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 18 ⟨3, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨3, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨3, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨3, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 0 18).region.getD 4 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨4, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 18 ⟨4, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨4, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨4, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨4, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
    · have hzero : (ReleasedInterior.seed 0 18).region.getD 5 0 = 0 := by decide +kernel
      have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨5, c⟩ = 0 := by decide +kernel
      have hv := mme_released_interior_zero_region_volume 0 18 ⟨5, c⟩ hzero (z + 1)
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      change (denominator : ℝ) ^ 4 * (q ⟨5, c⟩ : ℝ) ≤ 6 * (3952233 / 5000000 : ℝ) *
        (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨5, c⟩ w : ℝ)) +
          (∑ w, (ReleasedInterior.integerProfile 0 18 (z + 1) ⟨5, c⟩ w : ℝ) * (ones w : ℝ)) * Real.log 5)
      rw [hqzero, hv]
      simp only [Rat.cast_zero, mul_zero, le_refl]
  · rintro ⟨r, c⟩ z hz
    dsimp only
    fin_cases r
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨0, c⟩ ≤ theta ⟨0, c⟩ * v0 z := by decide +kernel
      have hqr : (q ⟨0, c⟩ : ℝ) ≤ (theta ⟨0, c⟩ : ℝ) * (v0 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region0_112_weight_rate_bound c z hz
      simp only [v0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨0, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨1, c⟩ ≤ theta ⟨1, c⟩ * v1 z := by decide +kernel
      have hqr : (q ⟨1, c⟩ : ℝ) ≤ (theta ⟨1, c⟩ : ℝ) * (v1 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region1_112_weight_rate_bound c z hz
      simp only [v1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨1, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hq : ∀ (c : ReleasedInterior.Split 18) (z : Fin 3),
          (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
          q ⟨2, c⟩ ≤ theta ⟨2, c⟩ * v2 z := by decide +kernel
      have hqr : (q ⟨2, c⟩ : ℝ) ≤ (theta ⟨2, c⟩ : ℝ) * (v2 z : ℝ) := by
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hq c z hz)
      have hv := mme_released_interior_owner0_cell18_region2_112_weight_rate_bound c z hz
      simp only [v2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hqr
      have ht : 0 ≤ (theta ⟨2, c⟩ : ℝ) := by
        simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
        positivity
      have h := hqr.trans (mul_le_mul_of_nonneg_left hv ht)
      simpa only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h
    · have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨3, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 18, theta ⟨3, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨3, c⟩ : ℝ) ≤ (theta ⟨3, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨4, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 18, theta ⟨4, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨4, c⟩ : ℝ) ≤ (theta ⟨4, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _
    · have hqzero : ∀ c : ReleasedInterior.Split 18, q ⟨5, c⟩ = 0 := by decide +kernel
      have htzero : ∀ c : ReleasedInterior.Split 18, theta ⟨5, c⟩ = 0 := by decide +kernel
      have h : ∀ x : ℝ, (q ⟨5, c⟩ : ℝ) ≤ (theta ⟨5, c⟩ : ℝ) * x := by
        intro x
        rw [hqzero, htzero]
        norm_num
      simp only [theta, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at h
      exact h _


#print axioms solution
