-- Prove2me | solution 1 for mme_released_joint_region1_mode1_parent_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T18:20:23.752271+00:00
-- url     : https://prove2.me/submissions/5d1863d4-99ce-46a9-84bb-bacd296dbc07

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_joint_owner0_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell13_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell14_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell18_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell19_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell22_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell25_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell26_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell27_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell28_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell32_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell37_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell40_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell11_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell12_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell14_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell18_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell19_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell22_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell25_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell26_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell27_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell28_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell32_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell36_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell40_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell11_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell12_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell19_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell20_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell22_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell27_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell31_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell33_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell36_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell37_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell40_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell13_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell14_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell20_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell22_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell26_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell31_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell33_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell36_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell37_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell40_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell11_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell12_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell14_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell18_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell19_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell20_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell25_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell27_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell32_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell33_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell36_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell37_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell40_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell10_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell13_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell14_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell15_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell20_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell21_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell22_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell26_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell28_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell31_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell32_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell36_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell37_region1_mode1_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell40_region1_mode1_parent_entropy_bound

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765410259, 0, 0, 1854757754, 1938482587, 1386294310, 0, 0, 1622431420, 1097528699, 0, 1925465737, 1386294361, 0, 0, 1082227723, 1718089130, 1870926555, 1386294361, 0, 0, 0, 1892797668, 0, 0, 0, 0, 1386294361, 0, 0, 1386294361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294012, 1924717949, 1846032720, 0, 1685963606, 1810518335, 0, 0, 1386294361, 1925666181, 0, 1147995191, 1644678228, 0, 0, 1386294361, 1870941328, 1719133143, 1124451691, 0, 0, 0, 1892814556, 0, 0, 0, 1386294360, 0, 0, 0, 1386294361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765392701, 1622419777, 1081570759, 0, 0, 1386294361, 0, 0, 0, 1097495263, 1717929236, 1891594773, 1386294361, 0, 0, 0, 0, 1870898822, 0, 0, 0, 1858917350, 0, 1386294361, 0, 0, 1945683146, 1386294361, 0, 0, 1386294358, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294124, 0, 0, 1123523107, 1644635241, 1810466163, 0, 0, 0, 0, 1718899589, 1147976023, 1685944167, 0, 0, 0, 1870906238, 0, 0, 0, 0, 1386294361, 0, 1859734028, 0, 0, 1386294361, 1945700199, 0, 0, 1386294358, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294013, 1386294361, 1386294361, 0, 1386294361, 1386294361, 0, 0, 1924726112, 1925681493, 1870916798, 1891620985, 0, 0, 0, 1847042608, 0, 1720399195, 0, 0, 0, 0, 1178877840, 1150422392, 0, 0, 1706944054, 1664833235, 0, 0, 1818075742, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294105, 0, 0, 1386294361, 1386294361, 1386294310, 0, 0, 0, 0, 1870905202, 1925524401, 1938460576, 0, 0, 0, 1720302837, 0, 1856558644, 0, 0, 1150050474, 1178878517, 0, 0, 0, 1664843063, 1706945828, 0, 0, 1818077762, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ := (boundNumerator j : ℚ) / 1000000000

/-- The actual pooled regional potential has a certified rational bound.
The complete parent-compatibility difference remains a separate obligation. -/
theorem solution :
    (denominator : ℝ) ^ 5 * (1515833441 / 1000000000 : ℝ) ≤
      parentPotential (parent_total 1) (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) := by
  have hcases : ∀ j : Fin 270, 0 < size 1 1 j →
      j ∈ ([10, 13, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 37, 40, 55, 56, 57, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 81, 85, 100, 101, 102, 105, 109, 110, 111, 112, 117, 121, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 166, 168, 171, 172, 175, 190, 191, 192, 194, 195, 198, 199, 200, 201, 205, 207, 212, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 253, 256, 257, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have hc : (denominator : ℚ) ^ 5 * (1515833441 / 1000000000 : ℚ) ≤
      ∑ j : Fin 270, (size 1 1 j : ℚ) * bound j := by decide +kernel
  have hcR := (Rat.cast_le (K := ℝ)).2 hc
  push_cast at hcR
  apply hcR.trans
  unfold parentPotential
  apply Finset.sum_le_sum
  intro j hj
  by_cases hz : size 1 1 j = 0
  · simp [hz]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hjcases := hcases j (Nat.pos_of_ne_zero hz)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjcases
  rcases hjcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst j
    have hb : bound (10 : Fin 270) = (1765410259 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (13 : Fin 270) = (1854757754 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell13_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (14 : Fin 270) = (1938482587 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell14_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (15 : Fin 270) = (1386294310 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (18 : Fin 270) = (1622431420 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell18_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (19 : Fin 270) = (1097528699 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell19_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (21 : Fin 270) = (1925465737 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (22 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell22_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (25 : Fin 270) = (1082227723 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell25_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (26 : Fin 270) = (1718089130 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell26_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (27 : Fin 270) = (1870926555 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell27_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (28 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell28_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (32 : Fin 270) = (1892797668 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell32_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (37 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell37_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (40 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell40_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (55 : Fin 270) = (1386294012 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (56 : Fin 270) = (1924717949 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell11_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (57 : Fin 270) = (1846032720 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell12_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (59 : Fin 270) = (1685963606 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell14_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (60 : Fin 270) = (1810518335 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (63 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell18_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (64 : Fin 270) = (1925666181 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell19_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (66 : Fin 270) = (1147995191 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (67 : Fin 270) = (1644678228 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell22_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (70 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell25_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (71 : Fin 270) = (1870941328 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell26_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (72 : Fin 270) = (1719133143 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell27_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (73 : Fin 270) = (1124451691 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell28_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (77 : Fin 270) = (1892814556 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell32_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (81 : Fin 270) = (1386294360 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell36_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (85 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell40_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (100 : Fin 270) = (1765392701 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (101 : Fin 270) = (1622419777 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell11_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (102 : Fin 270) = (1081570759 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell12_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (105 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (109 : Fin 270) = (1097495263 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell19_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (110 : Fin 270) = (1717929236 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell20_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (111 : Fin 270) = (1891594773 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (112 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell22_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (117 : Fin 270) = (1870898822 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell27_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (121 : Fin 270) = (1858917350 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell31_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (123 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell33_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (126 : Fin 270) = (1945683146 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell36_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (127 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell37_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (130 : Fin 270) = (1386294358 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell40_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (145 : Fin 270) = (1386294124 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (148 : Fin 270) = (1123523107 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell13_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (149 : Fin 270) = (1644635241 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell14_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (150 : Fin 270) = (1810466163 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (155 : Fin 270) = (1718899589 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell20_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (156 : Fin 270) = (1147976023 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (157 : Fin 270) = (1685944167 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell22_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (161 : Fin 270) = (1870906238 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell26_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (166 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell31_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (168 : Fin 270) = (1859734028 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell33_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (171 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell36_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (172 : Fin 270) = (1945700199 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell37_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (175 : Fin 270) = (1386294358 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell40_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (190 : Fin 270) = (1386294013 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (191 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell11_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (192 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell12_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (194 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell14_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (195 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (198 : Fin 270) = (1924726112 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell18_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (199 : Fin 270) = (1925681493 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell19_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (200 : Fin 270) = (1870916798 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell20_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (201 : Fin 270) = (1891620985 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (205 : Fin 270) = (1847042608 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell25_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (207 : Fin 270) = (1720399195 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell27_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (212 : Fin 270) = (1178877840 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell32_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (213 : Fin 270) = (1150422392 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell33_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (216 : Fin 270) = (1706944054 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell36_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (217 : Fin 270) = (1664833235 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell37_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (220 : Fin 270) = (1818075742 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell40_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (235 : Fin 270) = (1386294105 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell10_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (238 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell13_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (239 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell14_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (240 : Fin 270) = (1386294310 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell15_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (245 : Fin 270) = (1870905202 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell20_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (246 : Fin 270) = (1925524401 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell21_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (247 : Fin 270) = (1938460576 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell22_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (251 : Fin 270) = (1720302837 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell26_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (253 : Fin 270) = (1856558644 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell28_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (256 : Fin 270) = (1150050474 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell31_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (257 : Fin 270) = (1178878517 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell32_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (261 : Fin 270) = (1664843063 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell36_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (262 : Fin 270) = (1706945828 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell37_region1_mode1_parent_entropy_bound
  · subst j
    have hb : bound (265 : Fin 270) = (1818077762 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell40_region1_mode1_parent_entropy_bound


#print axioms solution
