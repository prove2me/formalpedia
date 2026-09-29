-- Prove2me | solution 1 for mme_released_joint_region0_mode2_compatibility_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T15:06:51.375277+00:00
-- url     : https://prove2.me/submissions/ca91ff96-a874-4eb5-a571-04379b83e02b

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_joint_compatibility_bound
import Theorems.Thm_mme_released_joint_owner0_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell11_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell12_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell14_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell18_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell19_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell22_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell25_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell26_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell27_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell28_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell32_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell36_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner0_cell40_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell13_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell14_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell18_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell19_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell22_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell25_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell26_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell27_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell28_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell32_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell37_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner1_cell40_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell11_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell12_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell14_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell18_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell19_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell20_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell25_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell27_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell32_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell33_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell36_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell37_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner2_cell40_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell13_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell14_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell20_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell22_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell26_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell28_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell31_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell32_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell36_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell37_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner3_cell40_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell11_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell12_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell19_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell20_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell22_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell27_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell31_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell33_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell36_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell37_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner4_cell40_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell10_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell13_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell14_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell15_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell20_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell21_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell22_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell26_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell31_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell33_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell36_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell37_region0_mode2_compatibility_entropy_bound
import Theorems.Thm_mme_released_joint_owner5_cell40_region0_mode2_compatibility_entropy_bound

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117073442, 3209031329, 3637377288, 0, 580745630, 76446577, 0, 0, 2840890962, 16226216070, 0, 7771625349, 1421779246, 0, 0, 679765615, 30491813308, 33309264694, 22534519628, 0, 0, 0, 26964115166, 0, 0, 0, 920833648, 0, 0, 0, 76810521, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75959945, 0, 0, 5032131155, 2978712473, 122067304, 0, 0, 1620857052, 966930795, 0, 5282498589, 2644492828, 0, 0, 26334607328, 35792863828, 28037201384, 2546646940, 0, 0, 0, 27214564927, 0, 0, 0, 0, 942165407, 0, 0, 76806768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117134165, 2852315801, 413883133, 0, 415131469, 76422055, 0, 0, 3177016684, 16483058817, 27441019115, 18202147624, 0, 0, 0, 3749846222, 0, 28601343382, 0, 0, 0, 0, 7801380960, 20784187690, 0, 0, 1003752551, 1232726581, 0, 0, 76839391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76028817, 0, 0, 2328213487, 2675449742, 122081483, 0, 0, 0, 0, 22098130865, 5426369725, 2987352934, 0, 0, 0, 26547139278, 0, 4986943299, 0, 0, 21040684777, 7843517054, 0, 0, 0, 1234359672, 1008772600, 0, 0, 76851082, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75991685, 1622876281, 26655045573, 0, 0, 76414217, 0, 0, 0, 1142073655, 33393729950, 17684233660, 400305988, 0, 0, 0, 0, 21692207445, 0, 0, 0, 5926789258, 0, 3375761096, 0, 0, 2708732929, 2371838447, 0, 0, 123078896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75986710, 0, 0, 22831427287, 1436664520, 76441395, 0, 0, 0, 0, 28949357624, 6794807360, 539684167, 0, 0, 0, 19057613573, 0, 0, 0, 0, 3317910368, 0, 6008823595, 0, 0, 2406969706, 2708175063, 0, 0, 123165240, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ := (boundNumerator j : ℚ) / 1000000000000

/-- The actual pooled regional potential has a certified rational bound.
The complete parent-compatibility difference remains a separate obligation. -/
theorem solution :
    compatibilityPotential 1 (integerProfile 0 1 2) ≤
      (denominator : ℝ) ^ 5 * (732983022 / 1000000000 : ℝ) := by
  have hcases : ∀ j : Fin 270, 0 < size 0 1 j →
      j ∈ ([10, 11, 12, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 36, 40, 55, 58, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 82, 85, 100, 101, 102, 104, 105, 108, 109, 110, 111, 115, 117, 122, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 163, 166, 167, 171, 172, 175, 190, 191, 192, 195, 199, 200, 201, 202, 207, 211, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 256, 258, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have h := mme_released_joint_compatibility_bound 0 1 1
    (fun j => (denominator : ℝ) ^ 5 * (bound j : ℝ))
    (fun j => mul_nonneg (by positivity) (by exact_mod_cast (show 0 ≤ bound j by unfold bound; positivity))) ?_
  · have hc : (∑ j : Fin 270, bound j) ≤ (732983022 / 1000000000 : ℚ) := by decide +kernel
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
      have hb : bound (10 : Fin 270) = (117073442 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (11 : Fin 270) : ℝ)
      have hb : bound (11 : Fin 270) = (3209031329 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell11_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (12 : Fin 270) : ℝ)
      have hb : bound (12 : Fin 270) = (3637377288 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell12_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (14 : Fin 270) : ℝ)
      have hb : bound (14 : Fin 270) = (580745630 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell14_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (15 : Fin 270) : ℝ)
      have hb : bound (15 : Fin 270) = (76446577 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (18 : Fin 270) : ℝ)
      have hb : bound (18 : Fin 270) = (2840890962 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell18_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (19 : Fin 270) : ℝ)
      have hb : bound (19 : Fin 270) = (16226216070 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell19_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (21 : Fin 270) : ℝ)
      have hb : bound (21 : Fin 270) = (7771625349 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (22 : Fin 270) : ℝ)
      have hb : bound (22 : Fin 270) = (1421779246 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell22_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (25 : Fin 270) : ℝ)
      have hb : bound (25 : Fin 270) = (679765615 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell25_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (26 : Fin 270) : ℝ)
      have hb : bound (26 : Fin 270) = (30491813308 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell26_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (27 : Fin 270) : ℝ)
      have hb : bound (27 : Fin 270) = (33309264694 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell27_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (28 : Fin 270) : ℝ)
      have hb : bound (28 : Fin 270) = (22534519628 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell28_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (32 : Fin 270) : ℝ)
      have hb : bound (32 : Fin 270) = (26964115166 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell32_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (36 : Fin 270) : ℝ)
      have hb : bound (36 : Fin 270) = (920833648 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell36_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (40 : Fin 270) : ℝ)
      have hb : bound (40 : Fin 270) = (76810521 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner0_cell40_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (55 : Fin 270) : ℝ)
      have hb : bound (55 : Fin 270) = (75959945 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (58 : Fin 270) : ℝ)
      have hb : bound (58 : Fin 270) = (5032131155 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell13_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (59 : Fin 270) : ℝ)
      have hb : bound (59 : Fin 270) = (2978712473 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell14_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (60 : Fin 270) : ℝ)
      have hb : bound (60 : Fin 270) = (122067304 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (63 : Fin 270) : ℝ)
      have hb : bound (63 : Fin 270) = (1620857052 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell18_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (64 : Fin 270) : ℝ)
      have hb : bound (64 : Fin 270) = (966930795 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell19_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (66 : Fin 270) : ℝ)
      have hb : bound (66 : Fin 270) = (5282498589 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (67 : Fin 270) : ℝ)
      have hb : bound (67 : Fin 270) = (2644492828 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell22_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (70 : Fin 270) : ℝ)
      have hb : bound (70 : Fin 270) = (26334607328 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell25_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (71 : Fin 270) : ℝ)
      have hb : bound (71 : Fin 270) = (35792863828 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell26_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (72 : Fin 270) : ℝ)
      have hb : bound (72 : Fin 270) = (28037201384 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell27_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (73 : Fin 270) : ℝ)
      have hb : bound (73 : Fin 270) = (2546646940 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell28_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (77 : Fin 270) : ℝ)
      have hb : bound (77 : Fin 270) = (27214564927 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell32_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (82 : Fin 270) : ℝ)
      have hb : bound (82 : Fin 270) = (942165407 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell37_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (85 : Fin 270) : ℝ)
      have hb : bound (85 : Fin 270) = (76806768 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner1_cell40_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (100 : Fin 270) : ℝ)
      have hb : bound (100 : Fin 270) = (117134165 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (101 : Fin 270) : ℝ)
      have hb : bound (101 : Fin 270) = (2852315801 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell11_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (102 : Fin 270) : ℝ)
      have hb : bound (102 : Fin 270) = (413883133 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell12_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (104 : Fin 270) : ℝ)
      have hb : bound (104 : Fin 270) = (415131469 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell14_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (105 : Fin 270) : ℝ)
      have hb : bound (105 : Fin 270) = (76422055 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (108 : Fin 270) : ℝ)
      have hb : bound (108 : Fin 270) = (3177016684 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell18_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (109 : Fin 270) : ℝ)
      have hb : bound (109 : Fin 270) = (16483058817 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell19_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (110 : Fin 270) : ℝ)
      have hb : bound (110 : Fin 270) = (27441019115 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell20_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (111 : Fin 270) : ℝ)
      have hb : bound (111 : Fin 270) = (18202147624 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (115 : Fin 270) : ℝ)
      have hb : bound (115 : Fin 270) = (3749846222 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell25_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (117 : Fin 270) : ℝ)
      have hb : bound (117 : Fin 270) = (28601343382 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell27_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (122 : Fin 270) : ℝ)
      have hb : bound (122 : Fin 270) = (7801380960 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell32_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (123 : Fin 270) : ℝ)
      have hb : bound (123 : Fin 270) = (20784187690 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell33_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (126 : Fin 270) : ℝ)
      have hb : bound (126 : Fin 270) = (1003752551 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell36_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (127 : Fin 270) : ℝ)
      have hb : bound (127 : Fin 270) = (1232726581 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell37_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (130 : Fin 270) : ℝ)
      have hb : bound (130 : Fin 270) = (76839391 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner2_cell40_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (145 : Fin 270) : ℝ)
      have hb : bound (145 : Fin 270) = (76028817 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (148 : Fin 270) : ℝ)
      have hb : bound (148 : Fin 270) = (2328213487 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell13_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (149 : Fin 270) : ℝ)
      have hb : bound (149 : Fin 270) = (2675449742 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell14_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (150 : Fin 270) : ℝ)
      have hb : bound (150 : Fin 270) = (122081483 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (155 : Fin 270) : ℝ)
      have hb : bound (155 : Fin 270) = (22098130865 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell20_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (156 : Fin 270) : ℝ)
      have hb : bound (156 : Fin 270) = (5426369725 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (157 : Fin 270) : ℝ)
      have hb : bound (157 : Fin 270) = (2987352934 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell22_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (161 : Fin 270) : ℝ)
      have hb : bound (161 : Fin 270) = (26547139278 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell26_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (163 : Fin 270) : ℝ)
      have hb : bound (163 : Fin 270) = (4986943299 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell28_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (166 : Fin 270) : ℝ)
      have hb : bound (166 : Fin 270) = (21040684777 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell31_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (167 : Fin 270) : ℝ)
      have hb : bound (167 : Fin 270) = (7843517054 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell32_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (171 : Fin 270) : ℝ)
      have hb : bound (171 : Fin 270) = (1234359672 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell36_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (172 : Fin 270) : ℝ)
      have hb : bound (172 : Fin 270) = (1008772600 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell37_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (175 : Fin 270) : ℝ)
      have hb : bound (175 : Fin 270) = (76851082 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner3_cell40_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (190 : Fin 270) : ℝ)
      have hb : bound (190 : Fin 270) = (75991685 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (191 : Fin 270) : ℝ)
      have hb : bound (191 : Fin 270) = (1622876281 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell11_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (192 : Fin 270) : ℝ)
      have hb : bound (192 : Fin 270) = (26655045573 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell12_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (195 : Fin 270) : ℝ)
      have hb : bound (195 : Fin 270) = (76414217 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (199 : Fin 270) : ℝ)
      have hb : bound (199 : Fin 270) = (1142073655 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell19_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (200 : Fin 270) : ℝ)
      have hb : bound (200 : Fin 270) = (33393729950 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell20_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (201 : Fin 270) : ℝ)
      have hb : bound (201 : Fin 270) = (17684233660 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (202 : Fin 270) : ℝ)
      have hb : bound (202 : Fin 270) = (400305988 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell22_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (207 : Fin 270) : ℝ)
      have hb : bound (207 : Fin 270) = (21692207445 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell27_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (211 : Fin 270) : ℝ)
      have hb : bound (211 : Fin 270) = (5926789258 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell31_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (213 : Fin 270) : ℝ)
      have hb : bound (213 : Fin 270) = (3375761096 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell33_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (216 : Fin 270) : ℝ)
      have hb : bound (216 : Fin 270) = (2708732929 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell36_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (217 : Fin 270) : ℝ)
      have hb : bound (217 : Fin 270) = (2371838447 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell37_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (220 : Fin 270) : ℝ)
      have hb : bound (220 : Fin 270) = (123078896 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner4_cell40_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (235 : Fin 270) : ℝ)
      have hb : bound (235 : Fin 270) = (75986710 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell10_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (238 : Fin 270) : ℝ)
      have hb : bound (238 : Fin 270) = (22831427287 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell13_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (239 : Fin 270) : ℝ)
      have hb : bound (239 : Fin 270) = (1436664520 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell14_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (240 : Fin 270) : ℝ)
      have hb : bound (240 : Fin 270) = (76441395 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell15_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (245 : Fin 270) : ℝ)
      have hb : bound (245 : Fin 270) = (28949357624 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell20_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (246 : Fin 270) : ℝ)
      have hb : bound (246 : Fin 270) = (6794807360 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell21_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (247 : Fin 270) : ℝ)
      have hb : bound (247 : Fin 270) = (539684167 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell22_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (251 : Fin 270) : ℝ)
      have hb : bound (251 : Fin 270) = (19057613573 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell26_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (256 : Fin 270) : ℝ)
      have hb : bound (256 : Fin 270) = (3317910368 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell31_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (258 : Fin 270) : ℝ)
      have hb : bound (258 : Fin 270) = (6008823595 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell33_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (261 : Fin 270) : ℝ)
      have hb : bound (261 : Fin 270) = (2406969706 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell36_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (262 : Fin 270) : ℝ)
      have hb : bound (262 : Fin 270) = (2708175063 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell37_region0_mode2_compatibility_entropy_bound
    · subst j
      change _ ≤ (denominator : ℝ) ^ 5 * (bound (265 : Fin 270) : ℝ)
      have hb : bound (265 : Fin 270) = (123165240 / 1000000000000 : ℚ) := by decide +kernel
      rw [hb]
      simpa only [yzMode, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using mme_released_joint_owner5_cell40_region0_mode2_compatibility_entropy_bound


#print axioms solution
