-- Prove2me | solution 1 for mme_released_interior_owner0_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T08:50:20.699013+00:00
-- url     : https://prove2.me/submissions/a7993855-ce4e-4d9d-838f-68db4bd3fafd

import Theorems.Thm_mme_released_interior_owner0_cell10_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell11_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell12_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell13_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell14_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell15_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell18_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell19_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell20_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell21_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell22_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell25_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell26_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell27_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell28_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell31_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell32_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell33_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell36_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell37_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner0_cell40_normalized_child_bounds
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- Every positive joint label of this owner has a complete normalized child
bound, with its exact sum in one common rational denominator. -/
theorem solution (s : Fin 45)
    (hpositive : 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), s))) :
    ∃ q : Cell 4 6 (ReleasedInterior.parent s) → ℝ,
      (∑ c, q c) = (((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41942266505765066845119296509892745276, 55960148815245111164349250089006417937, 65646885094610577637304411445936721185, 65561373954054183497095951507284147789, 55911993505513970825480047074998858661, 41939613802319576820170874981715874710, 0, 0, 55960392076064552927361628991215036970, 67273201889687490514281214960536360738, 69816807362384035064144414908798151062, 67314897118156470854361495542107070436, 55912991417199714022758749214305469906, 0, 0, 65642435443878275449957693952495410559, 69812444499594004357318466715627783069, 69809431905775731074119209362787023290, 65554412706622637282410640722699493476, 0, 0, 65504780410844592865789042904032273262, 67292200744174285977738282013168865587, 65501948167268801683250086657960827709, 0, 0, 55901106969644118414744706077370633296, 55901112135834816945175593488333904352, 0, 0, 41917562970434913210646190054161930518, 0, 0, 0, 0] : Fin 45 → ℕ) s : ℝ) / 2000000000000000000000000000000000000) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 0 s (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 0 s (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 0 s).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 0 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 0 s).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 0 s c.1 c.2 + ReleasedInterior.splitWeight 0 s c.1
            (complement (ReleasedInterior.parent_total s c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  fin_cases s
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (0 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (0 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (1 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (1 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (2 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (2 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (3 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (3 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (4 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (4 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (5 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (5 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (6 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (6 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (7 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (7 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (8 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (8 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (9 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (9 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell10_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41942266505765066845119296509892745276 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell11_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960148815245111164349250089006417937 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell12_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65646885094610577637304411445936721185 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell13_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65561373954054183497095951507284147789 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell14_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55911993505513970825480047074998858661 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell15_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41939613802319576820170874981715874710 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (16 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (16 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (17 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (17 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell18_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960392076064552927361628991215036970 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell19_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67273201889687490514281214960536360738 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell20_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69816807362384035064144414908798151062 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell21_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67314897118156470854361495542107070436 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell22_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55912991417199714022758749214305469906 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (23 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (23 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (24 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (24 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell25_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65642435443878275449957693952495410559 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell26_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69812444499594004357318466715627783069 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell27_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69809431905775731074119209362787023290 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell28_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65554412706622637282410640722699493476 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (29 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (29 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (30 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (30 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell31_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65504780410844592865789042904032273262 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell32_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67292200744174285977738282013168865587 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell33_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65501948167268801683250086657960827709 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (34 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (34 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (35 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (35 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell36_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55901106969644118414744706077370633296 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell37_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55901112135834816945175593488333904352 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (38 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (38 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (39 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (39 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner0_cell40_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41917562970434913210646190054161930518 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (41 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (41 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (42 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (42 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (43 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (43 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (44 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((0 : Fin 6), (44 : Fin 45))) at hpositive
    omega


#print axioms solution
