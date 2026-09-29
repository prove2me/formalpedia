-- Prove2me | solution 1 for mme_released_joint_region0_mode1_compatibility_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T14:16:52.266372+00:00
-- url     : https://prove2.me/submissions/fba833cd-e360-439e-8126-996264690ac7

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_joint_compatibility_bound
import Theorems.Thm_mme_released_joint_owner0_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell11_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell12_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell14_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell18_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell19_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell22_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell25_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell26_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell27_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell28_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell32_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell36_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell40_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell13_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell14_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell18_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell19_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell22_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell25_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell26_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell27_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell28_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell32_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell37_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell40_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell11_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell12_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell14_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell18_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell19_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell20_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell25_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell27_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell32_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell33_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell36_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell37_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell40_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell13_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell14_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell20_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell22_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell26_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell28_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell31_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell32_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell36_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell37_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell40_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell11_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell12_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell19_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell20_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell22_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell27_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell31_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell33_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell36_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell37_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell40_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell10_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell13_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell14_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell15_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell20_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell21_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell22_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell26_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell31_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell33_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell36_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell37_region0_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell40_region0_mode1_compatibility_entropy_bound

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75951634, 3981382063, 7188269610, 0, 540589734, 121725614, 0, 0, 2388576864, 35148441190, 0, 4867024140, 1718505781, 0, 0, 898036858, 34588948527, 31270159496, 17699883899, 0, 0, 0, 27168836384, 0, 0, 0, 645800398, 0, 0, 0, 76810521, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117086186, 0, 0, 9626930542, 3651918442, 76681450, 0, 0, 1925624509, 576204571, 0, 10466551335, 2185689109, 0, 0, 19814635020, 33573729605, 31792189647, 3236219255, 0, 0, 0, 27413190998, 0, 0, 0, 0, 660689897, 0, 0, 76806768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75992431, 2398187878, 547268309, 0, 291833422, 76422055, 0, 0, 3941941859, 35734439674, 31138056225, 18338739389, 0, 0, 0, 7408583178, 0, 26868980762, 0, 0, 0, 0, 5021201423, 16758645877, 0, 0, 952089651, 1540209736, 0, 0, 122585404, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76028817, 0, 0, 2962263381, 2211328541, 76694205, 0, 0, 0, 0, 25075235847, 10755564625, 3663230186, 0, 0, 0, 24933301208, 0, 9536922272, 0, 0, 16959775905, 5047654784, 0, 0, 0, 1542298717, 956757108, 0, 0, 122604060, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117135148, 1928017771, 20045376447, 0, 0, 76414217, 0, 0, 0, 680663828, 31316911038, 17808228365, 281368897, 0, 0, 0, 0, 24597159166, 0, 0, 0, 11091800077, 0, 4190006419, 0, 0, 3299471740, 1942724835, 0, 0, 77193901, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75986710, 0, 0, 17920602374, 1736370603, 121732448, 0, 0, 0, 0, 27165192620, 4254938499, 502231548, 0, 0, 0, 21618050814, 0, 0, 0, 0, 4120066118, 0, 11244321855, 0, 0, 1971501037, 3299196859, 0, 0, 77248053, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ := (boundNumerator j : ℚ) / 1000000000000

/-- The actual pooled regional potential has a certified rational bound.
The complete parent-compatibility difference remains a separate obligation. -/
theorem solution :
    compatibilityPotential 0 (integerProfile 0 1 1) ≤
      (denominator : ℝ) ^ 5 * (780267839 / 1000000000 : ℝ) := by
  have hcases : ∀ j : Fin 270, 0 < size 0 1 j →
      j ∈ ([10, 11, 12, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 36, 40, 55, 58, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 82, 85, 100, 101, 102, 104, 105, 108, 109, 110, 111, 115, 117, 122, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 163, 166, 167, 171, 172, 175, 190, 191, 192, 195, 199, 200, 201, 202, 207, 211, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 256, 258, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have h := mme_released_joint_compatibility_bound 0 1 0
    (fun j => (denominator : ℝ) ^ 5 * (bound j : ℝ))
    (fun j => mul_nonneg (by positivity) (by exact_mod_cast (show 0 ≤ bound j by unfold bound; positivity))) ?_
  · have hc : (∑ j : Fin 270, bound j) ≤ (780267839 / 1000000000 : ℚ) := by decide +kernel
    have hcR := (Rat.cast_le (K := ℝ)).2 hc
    push_cast at hcR
    rw [← Finset.mul_sum] at h
    exact h.trans (mul_le_mul_of_nonneg_left hcR (by positivity))
  · intro j hj
    have hjcases := hcases j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjcases
    rcases hjcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (10 : Fin 270) : ℝ)
      have hb : bound (10 : Fin 270) = (75951634 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (11 : Fin 270) : ℝ)
      have hb : bound (11 : Fin 270) = (3981382063 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell11_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (12 : Fin 270) : ℝ)
      have hb : bound (12 : Fin 270) = (7188269610 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell12_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (14 : Fin 270) : ℝ)
      have hb : bound (14 : Fin 270) = (540589734 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell14_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (15 : Fin 270) : ℝ)
      have hb : bound (15 : Fin 270) = (121725614 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (18 : Fin 270) : ℝ)
      have hb : bound (18 : Fin 270) = (2388576864 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell18_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (19 : Fin 270) : ℝ)
      have hb : bound (19 : Fin 270) = (35148441190 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell19_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (21 : Fin 270) : ℝ)
      have hb : bound (21 : Fin 270) = (4867024140 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (22 : Fin 270) : ℝ)
      have hb : bound (22 : Fin 270) = (1718505781 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell22_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (25 : Fin 270) : ℝ)
      have hb : bound (25 : Fin 270) = (898036858 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell25_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (26 : Fin 270) : ℝ)
      have hb : bound (26 : Fin 270) = (34588948527 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell26_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (27 : Fin 270) : ℝ)
      have hb : bound (27 : Fin 270) = (31270159496 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell27_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (28 : Fin 270) : ℝ)
      have hb : bound (28 : Fin 270) = (17699883899 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell28_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (32 : Fin 270) : ℝ)
      have hb : bound (32 : Fin 270) = (27168836384 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell32_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (36 : Fin 270) : ℝ)
      have hb : bound (36 : Fin 270) = (645800398 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell36_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (40 : Fin 270) : ℝ)
      have hb : bound (40 : Fin 270) = (76810521 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell40_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (55 : Fin 270) : ℝ)
      have hb : bound (55 : Fin 270) = (117086186 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (58 : Fin 270) : ℝ)
      have hb : bound (58 : Fin 270) = (9626930542 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell13_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (59 : Fin 270) : ℝ)
      have hb : bound (59 : Fin 270) = (3651918442 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell14_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (60 : Fin 270) : ℝ)
      have hb : bound (60 : Fin 270) = (76681450 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (63 : Fin 270) : ℝ)
      have hb : bound (63 : Fin 270) = (1925624509 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell18_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (64 : Fin 270) : ℝ)
      have hb : bound (64 : Fin 270) = (576204571 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell19_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (66 : Fin 270) : ℝ)
      have hb : bound (66 : Fin 270) = (10466551335 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (67 : Fin 270) : ℝ)
      have hb : bound (67 : Fin 270) = (2185689109 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell22_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (70 : Fin 270) : ℝ)
      have hb : bound (70 : Fin 270) = (19814635020 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell25_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (71 : Fin 270) : ℝ)
      have hb : bound (71 : Fin 270) = (33573729605 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell26_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (72 : Fin 270) : ℝ)
      have hb : bound (72 : Fin 270) = (31792189647 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell27_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (73 : Fin 270) : ℝ)
      have hb : bound (73 : Fin 270) = (3236219255 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell28_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (77 : Fin 270) : ℝ)
      have hb : bound (77 : Fin 270) = (27413190998 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell32_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (82 : Fin 270) : ℝ)
      have hb : bound (82 : Fin 270) = (660689897 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell37_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (85 : Fin 270) : ℝ)
      have hb : bound (85 : Fin 270) = (76806768 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell40_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (100 : Fin 270) : ℝ)
      have hb : bound (100 : Fin 270) = (75992431 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (101 : Fin 270) : ℝ)
      have hb : bound (101 : Fin 270) = (2398187878 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell11_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (102 : Fin 270) : ℝ)
      have hb : bound (102 : Fin 270) = (547268309 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell12_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (104 : Fin 270) : ℝ)
      have hb : bound (104 : Fin 270) = (291833422 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell14_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (105 : Fin 270) : ℝ)
      have hb : bound (105 : Fin 270) = (76422055 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (108 : Fin 270) : ℝ)
      have hb : bound (108 : Fin 270) = (3941941859 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell18_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (109 : Fin 270) : ℝ)
      have hb : bound (109 : Fin 270) = (35734439674 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell19_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (110 : Fin 270) : ℝ)
      have hb : bound (110 : Fin 270) = (31138056225 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell20_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (111 : Fin 270) : ℝ)
      have hb : bound (111 : Fin 270) = (18338739389 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (115 : Fin 270) : ℝ)
      have hb : bound (115 : Fin 270) = (7408583178 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell25_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (117 : Fin 270) : ℝ)
      have hb : bound (117 : Fin 270) = (26868980762 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell27_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (122 : Fin 270) : ℝ)
      have hb : bound (122 : Fin 270) = (5021201423 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell32_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (123 : Fin 270) : ℝ)
      have hb : bound (123 : Fin 270) = (16758645877 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell33_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (126 : Fin 270) : ℝ)
      have hb : bound (126 : Fin 270) = (952089651 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell36_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (127 : Fin 270) : ℝ)
      have hb : bound (127 : Fin 270) = (1540209736 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell37_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (130 : Fin 270) : ℝ)
      have hb : bound (130 : Fin 270) = (122585404 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell40_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (145 : Fin 270) : ℝ)
      have hb : bound (145 : Fin 270) = (76028817 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (148 : Fin 270) : ℝ)
      have hb : bound (148 : Fin 270) = (2962263381 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell13_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (149 : Fin 270) : ℝ)
      have hb : bound (149 : Fin 270) = (2211328541 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell14_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (150 : Fin 270) : ℝ)
      have hb : bound (150 : Fin 270) = (76694205 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (155 : Fin 270) : ℝ)
      have hb : bound (155 : Fin 270) = (25075235847 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell20_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (156 : Fin 270) : ℝ)
      have hb : bound (156 : Fin 270) = (10755564625 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (157 : Fin 270) : ℝ)
      have hb : bound (157 : Fin 270) = (3663230186 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell22_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (161 : Fin 270) : ℝ)
      have hb : bound (161 : Fin 270) = (24933301208 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell26_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (163 : Fin 270) : ℝ)
      have hb : bound (163 : Fin 270) = (9536922272 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell28_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (166 : Fin 270) : ℝ)
      have hb : bound (166 : Fin 270) = (16959775905 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell31_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (167 : Fin 270) : ℝ)
      have hb : bound (167 : Fin 270) = (5047654784 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell32_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (171 : Fin 270) : ℝ)
      have hb : bound (171 : Fin 270) = (1542298717 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell36_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (172 : Fin 270) : ℝ)
      have hb : bound (172 : Fin 270) = (956757108 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell37_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (175 : Fin 270) : ℝ)
      have hb : bound (175 : Fin 270) = (122604060 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell40_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (190 : Fin 270) : ℝ)
      have hb : bound (190 : Fin 270) = (117135148 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (191 : Fin 270) : ℝ)
      have hb : bound (191 : Fin 270) = (1928017771 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell11_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (192 : Fin 270) : ℝ)
      have hb : bound (192 : Fin 270) = (20045376447 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell12_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (195 : Fin 270) : ℝ)
      have hb : bound (195 : Fin 270) = (76414217 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (199 : Fin 270) : ℝ)
      have hb : bound (199 : Fin 270) = (680663828 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell19_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (200 : Fin 270) : ℝ)
      have hb : bound (200 : Fin 270) = (31316911038 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell20_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (201 : Fin 270) : ℝ)
      have hb : bound (201 : Fin 270) = (17808228365 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (202 : Fin 270) : ℝ)
      have hb : bound (202 : Fin 270) = (281368897 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell22_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (207 : Fin 270) : ℝ)
      have hb : bound (207 : Fin 270) = (24597159166 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell27_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (211 : Fin 270) : ℝ)
      have hb : bound (211 : Fin 270) = (11091800077 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell31_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (213 : Fin 270) : ℝ)
      have hb : bound (213 : Fin 270) = (4190006419 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell33_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (216 : Fin 270) : ℝ)
      have hb : bound (216 : Fin 270) = (3299471740 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell36_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (217 : Fin 270) : ℝ)
      have hb : bound (217 : Fin 270) = (1942724835 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell37_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (220 : Fin 270) : ℝ)
      have hb : bound (220 : Fin 270) = (77193901 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell40_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (235 : Fin 270) : ℝ)
      have hb : bound (235 : Fin 270) = (75986710 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell10_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (238 : Fin 270) : ℝ)
      have hb : bound (238 : Fin 270) = (17920602374 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell13_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (239 : Fin 270) : ℝ)
      have hb : bound (239 : Fin 270) = (1736370603 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell14_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (240 : Fin 270) : ℝ)
      have hb : bound (240 : Fin 270) = (121732448 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell15_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (245 : Fin 270) : ℝ)
      have hb : bound (245 : Fin 270) = (27165192620 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell20_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (246 : Fin 270) : ℝ)
      have hb : bound (246 : Fin 270) = (4254938499 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell21_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (247 : Fin 270) : ℝ)
      have hb : bound (247 : Fin 270) = (502231548 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell22_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (251 : Fin 270) : ℝ)
      have hb : bound (251 : Fin 270) = (21618050814 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell26_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (256 : Fin 270) : ℝ)
      have hb : bound (256 : Fin 270) = (4120066118 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell31_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (258 : Fin 270) : ℝ)
      have hb : bound (258 : Fin 270) = (11244321855 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell33_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (261 : Fin 270) : ℝ)
      have hb : bound (261 : Fin 270) = (1971501037 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell36_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (262 : Fin 270) : ℝ)
      have hb : bound (262 : Fin 270) = (3299196859 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell37_region0_mode1_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (265 : Fin 270) : ℝ)
      have hb : bound (265 : Fin 270) = (77248053 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell40_region0_mode1_compatibility_entropy_bound


#print axioms solution
