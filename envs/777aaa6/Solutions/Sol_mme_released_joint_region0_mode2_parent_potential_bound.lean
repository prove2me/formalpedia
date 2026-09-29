-- Prove2me | solution 1 for mme_released_joint_region0_mode2_parent_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:26:59.401309+00:00
-- url     : https://prove2.me/submissions/589fdc12-f148-4e47-9e0c-47e6a05fd73f

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_joint_owner0_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell11_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell12_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell14_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell18_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell19_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell22_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell25_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell26_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell27_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell28_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell32_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell36_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell40_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell13_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell14_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell18_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell19_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell22_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell25_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell26_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell27_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell28_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell32_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell37_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell40_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell11_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell12_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell14_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell18_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell19_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell20_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell25_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell27_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell32_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell33_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell36_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell37_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell40_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell13_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell14_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell20_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell22_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell26_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell28_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell31_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell32_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell36_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell37_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell40_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell11_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell12_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell19_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell20_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell22_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell27_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell31_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell33_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell36_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell37_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell40_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell10_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell13_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell14_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell15_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell20_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell21_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell22_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell26_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell31_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell33_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell36_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell37_region0_mode2_parent_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell40_region0_mode2_parent_entropy_bound

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765811655, 1623430402, 1101732880, 0, 1897618512, 1386294278, 0, 0, 1623454305, 1044634418, 0, 1885619059, 1386294361, 0, 0, 1102485318, 1702569796, 1864130542, 1386294361, 0, 0, 0, 1893018628, 0, 0, 0, 1903207513, 0, 0, 0, 1386294361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386293946, 0, 0, 1141323913, 1646480914, 1810537961, 0, 0, 1386294361, 1882662410, 0, 1099078247, 1646282822, 0, 0, 1386294361, 1864164571, 1703358992, 1142198564, 0, 0, 0, 1893038514, 0, 0, 0, 0, 1903216613, 0, 0, 1386294360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1765793540, 1623444893, 1101701590, 0, 1897591598, 1386294361, 0, 0, 1623519147, 1044441389, 1702300384, 1891808789, 0, 0, 0, 1102309684, 0, 1864124999, 0, 0, 0, 0, 1887216343, 1386294361, 0, 0, 1903220388, 1386294361, 0, 0, 1386294360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386294119, 0, 0, 1140952280, 1646236018, 1810486064, 0, 0, 0, 0, 1702837997, 1099033240, 1646458756, 0, 0, 0, 1864158801, 0, 1142447057, 0, 0, 1386294361, 1887244767, 0, 0, 0, 1386294361, 1903230168, 0, 0, 1386294360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386293947, 1386294361, 1386294361, 0, 0, 1386294361, 0, 0, 0, 1882691913, 1864185795, 1891839025, 1897574989, 0, 0, 0, 0, 1704122683, 0, 0, 0, 1166622465, 0, 1166604829, 0, 0, 1659076672, 1658712817, 0, 0, 1818475151, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1386293957, 0, 0, 1386294361, 1386294361, 1386294278, 0, 0, 0, 0, 1864183011, 1885685658, 1897595368, 0, 0, 0, 1703864896, 0, 0, 0, 0, 1166103044, 0, 1167102280, 0, 0, 1658714426, 1659082969, 0, 0, 1818475134, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ := (boundNumerator j : ℚ) / 1000000000

/-- The actual pooled regional potential has a certified rational bound.
The complete parent-compatibility difference remains a separate obligation. -/
theorem solution :
    (denominator : ℝ) ^ 5 * (1468835613 / 1000000000 : ℝ) ≤
      parentPotential (parent_total 0) (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) := by
  have hcases : ∀ j : Fin 270, 0 < size 0 1 j →
      j ∈ ([10, 11, 12, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 36, 40, 55, 58, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 82, 85, 100, 101, 102, 104, 105, 108, 109, 110, 111, 115, 117, 122, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 163, 166, 167, 171, 172, 175, 190, 191, 192, 195, 199, 200, 201, 202, 207, 211, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 256, 258, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have hc : (denominator : ℚ) ^ 5 * (1468835613 / 1000000000 : ℚ) ≤
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
    have hb : bound (10 : Fin 270) = (1765811655 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (11 : Fin 270) = (1623430402 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell11_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (12 : Fin 270) = (1101732880 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell12_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (14 : Fin 270) = (1897618512 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell14_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (15 : Fin 270) = (1386294278 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (18 : Fin 270) = (1623454305 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell18_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (19 : Fin 270) = (1044634418 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell19_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (21 : Fin 270) = (1885619059 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (22 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell22_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (25 : Fin 270) = (1102485318 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell25_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (26 : Fin 270) = (1702569796 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell26_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (27 : Fin 270) = (1864130542 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell27_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (28 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell28_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (32 : Fin 270) = (1893018628 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell32_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (36 : Fin 270) = (1903207513 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell36_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (40 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell40_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (55 : Fin 270) = (1386293946 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (58 : Fin 270) = (1141323913 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell13_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (59 : Fin 270) = (1646480914 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell14_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (60 : Fin 270) = (1810537961 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (63 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell18_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (64 : Fin 270) = (1882662410 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell19_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (66 : Fin 270) = (1099078247 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (67 : Fin 270) = (1646282822 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell22_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (70 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell25_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (71 : Fin 270) = (1864164571 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell26_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (72 : Fin 270) = (1703358992 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell27_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (73 : Fin 270) = (1142198564 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell28_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (77 : Fin 270) = (1893038514 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell32_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (82 : Fin 270) = (1903216613 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell37_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (85 : Fin 270) = (1386294360 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell40_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (100 : Fin 270) = (1765793540 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (101 : Fin 270) = (1623444893 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell11_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (102 : Fin 270) = (1101701590 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell12_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (104 : Fin 270) = (1897591598 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell14_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (105 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (108 : Fin 270) = (1623519147 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell18_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (109 : Fin 270) = (1044441389 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell19_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (110 : Fin 270) = (1702300384 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell20_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (111 : Fin 270) = (1891808789 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (115 : Fin 270) = (1102309684 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell25_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (117 : Fin 270) = (1864124999 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell27_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (122 : Fin 270) = (1887216343 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell32_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (123 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell33_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (126 : Fin 270) = (1903220388 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell36_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (127 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell37_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (130 : Fin 270) = (1386294360 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell40_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (145 : Fin 270) = (1386294119 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (148 : Fin 270) = (1140952280 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell13_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (149 : Fin 270) = (1646236018 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell14_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (150 : Fin 270) = (1810486064 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (155 : Fin 270) = (1702837997 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell20_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (156 : Fin 270) = (1099033240 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (157 : Fin 270) = (1646458756 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell22_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (161 : Fin 270) = (1864158801 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell26_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (163 : Fin 270) = (1142447057 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell28_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (166 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell31_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (167 : Fin 270) = (1887244767 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell32_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (171 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell36_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (172 : Fin 270) = (1903230168 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell37_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (175 : Fin 270) = (1386294360 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell40_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (190 : Fin 270) = (1386293947 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (191 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell11_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (192 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell12_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (195 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (199 : Fin 270) = (1882691913 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell19_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (200 : Fin 270) = (1864185795 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell20_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (201 : Fin 270) = (1891839025 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (202 : Fin 270) = (1897574989 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell22_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (207 : Fin 270) = (1704122683 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell27_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (211 : Fin 270) = (1166622465 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell31_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (213 : Fin 270) = (1166604829 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell33_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (216 : Fin 270) = (1659076672 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell36_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (217 : Fin 270) = (1658712817 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell37_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (220 : Fin 270) = (1818475151 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell40_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (235 : Fin 270) = (1386293957 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell10_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (238 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell13_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (239 : Fin 270) = (1386294361 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell14_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (240 : Fin 270) = (1386294278 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell15_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (245 : Fin 270) = (1864183011 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell20_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (246 : Fin 270) = (1885685658 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell21_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (247 : Fin 270) = (1897595368 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell22_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (251 : Fin 270) = (1703864896 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell26_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (256 : Fin 270) = (1166103044 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell31_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (258 : Fin 270) = (1167102280 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell33_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (261 : Fin 270) = (1658714426 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell36_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (262 : Fin 270) = (1659082969 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell37_region0_mode2_parent_entropy_bound
  · subst j
    have hb : bound (265 : Fin 270) = (1818475134 / 1000000000 : ℚ) := by decide +kernel
    rw [hb]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell40_region0_mode2_parent_entropy_bound


#print axioms solution
