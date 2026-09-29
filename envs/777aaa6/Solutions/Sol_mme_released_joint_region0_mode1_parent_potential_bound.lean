-- Prove2me | solution 1 for mme_released_joint_region0_mode1_parent_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:22:58.390553+00:00
-- url     : https://prove2.me/submissions/98c1aff5-efdc-4201-a9a1-1c0b570a4c8a

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_joint_owner0_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell11_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell12_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell14_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell18_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell19_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell22_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell25_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell26_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell27_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell28_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell32_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell36_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell40_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell13_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell14_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell18_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell19_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell22_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell25_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell26_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell27_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell28_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell32_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell37_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell40_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell11_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell12_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell14_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell18_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell19_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell20_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell25_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell27_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell32_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell33_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell36_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell37_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell40_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell13_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell14_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell20_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell22_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell26_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell28_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell31_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell32_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell36_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell37_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell40_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell11_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell12_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell19_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell20_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell22_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell27_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell31_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell33_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell36_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell37_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell40_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell10_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell13_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell14_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell15_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell20_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell21_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell22_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell26_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell31_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell33_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell36_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell37_region0_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell40_region0_mode1_parent_entropy_bound

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294361, 1924721357, 1846096944, 0, 1685891914, 1810146650, 0, 0, 1386294361, 1925653378, 0, 1147875381, 1644791878, 0, 0, 1386294361, 1870941398, 1719159879, 1124369009, 0, 0, 0, 1892814755, 0, 0, 0, 1386294361, 0, 0, 0, 1386294361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765788364, 0, 0, 1854838722, 1938435413, 1386294361, 0, 0, 1622457673, 1097565140, 0, 1925452156, 1386294361, 0, 0, 1082199096, 1718077636, 1870922218, 1386294361, 0, 0, 0, 1892796081, 0, 0, 0, 0, 1386294361, 0, 0, 1386294360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294361, 1386294361, 1386294361, 0, 1386294361, 1386294361, 0, 0, 1924729207, 1925701689, 1870916012, 1891625354, 0, 0, 0, 1846995201, 0, 1720416955, 0, 0, 0, 0, 1178888707, 1150434821, 0, 0, 1706953920, 1664870569, 0, 0, 1818103397, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294130, 0, 0, 1386294361, 1386294361, 1386294361, 0, 0, 0, 0, 1870904356, 1925527591, 1938448059, 0, 0, 0, 1720317252, 0, 1856550568, 0, 0, 1150056410, 1178891140, 0, 0, 0, 1664880640, 1706957259, 0, 0, 1818103373, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765787538, 1622445123, 1081701097, 0, 0, 1386294361, 0, 0, 0, 1097600389, 1717949552, 1891590744, 1386294361, 0, 0, 0, 0, 1870897762, 0, 0, 0, 1858933857, 0, 1386294361, 0, 0, 1945684373, 1386294361, 0, 0, 1386294359, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386293787, 0, 0, 1123569802, 1644686715, 1810284757, 0, 0, 0, 0, 1718924784, 1148051791, 1685792664, 0, 0, 0, 1870904973, 0, 0, 0, 0, 1386294361, 0, 1859688693, 0, 0, 1386294361, 1945701964, 0, 0, 1386294359, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ := (boundNumerator j : ℚ) / 1000000000

/-- The actual pooled regional potential has a certified rational bound.
The complete parent-compatibility difference remains a separate obligation. -/
theorem solution :
    (denominator : ℝ) ^ 5 * (1516120430 / 1000000000 : ℝ) ≤
      parentPotential (parent_total 0) (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) := by
  have hcases : ∀ j : Fin 270, 0 < size 0 1 j →
      j ∈ ([10, 11, 12, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 36, 40, 55, 58, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 82, 85, 100, 101, 102, 104, 105, 108, 109, 110, 111, 115, 117, 122, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 163, 166, 167, 171, 172, 175, 190, 191, 192, 195, 199, 200, 201, 202, 207, 211, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 256, 258, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have hc : (denominator : ℚ) ^ 5 * (1516120430 / 1000000000 : ℚ) ≤
      ∑ j : Fin 270, (size 0 1 j : ℚ) * bound j := by decide +kernel
  have hcR := (Rat.cast_le (K := ℝ)).2 hc
  push_cast at hcR
  apply hcR.trans
  unfold parentPotential
  apply Finset.sum_le_sum
  intro j hj
  by_cases hz : size 0 1 j = 0
  · simp [hz]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hjcases := hcases j (Nat.pos_of_ne_zero hz)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjcases
  rcases hjcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst j
    have hb : bound (10 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (11 : Fin 270) = (1924721357 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell11_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (12 : Fin 270) = (1846096944 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell12_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (14 : Fin 270) = (1685891914 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell14_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (15 : Fin 270) = (1810146650 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (18 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell18_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (19 : Fin 270) = (1925653378 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell19_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (21 : Fin 270) = (1147875381 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (22 : Fin 270) = (1644791878 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell22_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (25 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell25_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (26 : Fin 270) = (1870941398 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell26_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (27 : Fin 270) = (1719159879 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell27_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (28 : Fin 270) = (1124369009 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell28_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (32 : Fin 270) = (1892814755 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell32_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (36 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell36_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (40 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell40_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (55 : Fin 270) = (1765788364 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (58 : Fin 270) = (1854838722 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell13_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (59 : Fin 270) = (1938435413 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell14_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (60 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (63 : Fin 270) = (1622457673 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell18_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (64 : Fin 270) = (1097565140 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell19_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (66 : Fin 270) = (1925452156 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (67 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell22_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (70 : Fin 270) = (1082199096 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell25_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (71 : Fin 270) = (1718077636 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell26_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (72 : Fin 270) = (1870922218 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell27_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (73 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell28_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (77 : Fin 270) = (1892796081 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell32_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (82 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell37_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (85 : Fin 270) = (1386294360 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell40_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (100 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (101 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell11_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (102 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell12_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (104 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell14_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (105 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (108 : Fin 270) = (1924729207 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell18_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (109 : Fin 270) = (1925701689 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell19_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (110 : Fin 270) = (1870916012 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell20_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (111 : Fin 270) = (1891625354 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (115 : Fin 270) = (1846995201 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell25_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (117 : Fin 270) = (1720416955 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell27_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (122 : Fin 270) = (1178888707 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell32_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (123 : Fin 270) = (1150434821 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell33_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (126 : Fin 270) = (1706953920 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell36_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (127 : Fin 270) = (1664870569 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell37_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (130 : Fin 270) = (1818103397 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell40_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (145 : Fin 270) = (1386294130 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (148 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell13_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (149 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell14_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (150 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (155 : Fin 270) = (1870904356 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell20_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (156 : Fin 270) = (1925527591 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (157 : Fin 270) = (1938448059 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell22_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (161 : Fin 270) = (1720317252 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell26_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (163 : Fin 270) = (1856550568 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell28_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (166 : Fin 270) = (1150056410 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell31_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (167 : Fin 270) = (1178891140 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell32_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (171 : Fin 270) = (1664880640 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell36_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (172 : Fin 270) = (1706957259 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell37_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (175 : Fin 270) = (1818103373 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell40_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (190 : Fin 270) = (1765787538 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (191 : Fin 270) = (1622445123 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell11_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (192 : Fin 270) = (1081701097 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell12_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (195 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (199 : Fin 270) = (1097600389 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell19_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (200 : Fin 270) = (1717949552 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell20_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (201 : Fin 270) = (1891590744 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (202 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell22_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (207 : Fin 270) = (1870897762 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell27_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (211 : Fin 270) = (1858933857 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell31_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (213 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell33_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (216 : Fin 270) = (1945684373 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell36_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (217 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell37_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (220 : Fin 270) = (1386294359 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell40_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (235 : Fin 270) = (1386293787 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell10_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (238 : Fin 270) = (1123569802 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell13_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (239 : Fin 270) = (1644686715 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell14_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (240 : Fin 270) = (1810284757 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell15_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (245 : Fin 270) = (1718924784 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell20_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (246 : Fin 270) = (1148051791 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell21_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (247 : Fin 270) = (1685792664 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell22_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (251 : Fin 270) = (1870904973 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell26_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (256 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell31_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (258 : Fin 270) = (1859688693 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell33_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (261 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell36_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (262 : Fin 270) = (1945701964 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell37_region0_mode1_parent_entropy_bound
  · subst j
    have hb : bound (265 : Fin 270) = (1386294359 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell40_region0_mode1_parent_entropy_bound


#print axioms solution
