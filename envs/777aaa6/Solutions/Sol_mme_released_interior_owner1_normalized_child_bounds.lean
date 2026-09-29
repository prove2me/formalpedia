-- Prove2me | solution 1 for mme_released_interior_owner1_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:12:29.414985+00:00
-- url     : https://prove2.me/submissions/f13478f5-b70b-457f-9fd8-f8f4c152ba79

import Theorems.Thm_mme_released_interior_owner1_cell10_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell11_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell12_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell13_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell14_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell15_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell18_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell19_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell20_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell21_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell22_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell25_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell26_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell27_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell28_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell31_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell32_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell33_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell36_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell37_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner1_cell40_normalized_child_bounds
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- Every positive joint label of this owner has a complete normalized child
bound, with its exact sum in one common rational denominator. -/
theorem solution (s : Fin 45)
    (hpositive : 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), s))) :
    ∃ q : Cell 4 6 (ReleasedInterior.parent s) → ℝ,
      (∑ c, q c) = (((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41936625791982189295853642842544010244, 55960024266904920534779947427032743063, 65646721612642746117925855429430730288, 65561486069791259816112943269062379582, 55911244358753157851334490881868041732, 41941590907020486043898285958168410636, 0, 0, 55960213564520648431261767265675625400, 67271108486500005396871752205047141192, 69817008934465431323988296547464392630, 67320075313398167398769552389158913672, 55911428065194343912228844471904701919, 0, 0, 65642452642500346547143187949709706891, 69813092918148009790587964881485859451, 69809694959696330725457452345086518726, 65554123157703815350632225063546706378, 0, 0, 65505027970568689609427015128078822858, 67291952083071538395731695266228931603, 65502119145810669596193517196176262976, 0, 0, 55900458587968497844893111876861295759, 55902291884796781677654962750481409342, 0, 0, 41917616249553886394834144924812756541, 0, 0, 0, 0] : Fin 45 → ℕ) s : ℝ) / 2000000000000000000000000000000000000) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 1 s (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 1 s (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 1 s).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 1 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 1 s).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 1 s c.1 c.2 + ReleasedInterior.splitWeight 1 s c.1
            (complement (ReleasedInterior.parent_total s c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  fin_cases s
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (0 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (0 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (1 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (1 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (2 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (2 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (3 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (3 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (4 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (4 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (5 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (5 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (6 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (6 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (7 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (7 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (8 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (8 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (9 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (9 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell10_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41936625791982189295853642842544010244 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell11_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960024266904920534779947427032743063 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell12_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65646721612642746117925855429430730288 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell13_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65561486069791259816112943269062379582 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell14_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55911244358753157851334490881868041732 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell15_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41941590907020486043898285958168410636 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (16 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (16 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (17 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (17 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell18_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960213564520648431261767265675625400 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell19_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67271108486500005396871752205047141192 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell20_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69817008934465431323988296547464392630 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell21_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67320075313398167398769552389158913672 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell22_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55911428065194343912228844471904701919 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (23 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (23 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (24 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (24 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell25_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65642452642500346547143187949709706891 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell26_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69813092918148009790587964881485859451 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell27_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69809694959696330725457452345086518726 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell28_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65554123157703815350632225063546706378 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (29 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (29 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (30 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (30 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell31_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65505027970568689609427015128078822858 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell32_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67291952083071538395731695266228931603 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell33_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65502119145810669596193517196176262976 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (34 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (34 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (35 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (35 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell36_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55900458587968497844893111876861295759 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell37_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55902291884796781677654962750481409342 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (38 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (38 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (39 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (39 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner1_cell40_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41917616249553886394834144924812756541 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (41 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (41 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (42 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (42 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (43 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (43 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (44 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((1 : Fin 6), (44 : Fin 45))) at hpositive
    omega


#print axioms solution
