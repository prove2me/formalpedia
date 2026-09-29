-- Prove2me | solution 1 for mme_released_interior_owner2_normalized_child_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:01:57.148808+00:00
-- url     : https://prove2.me/submissions/21aaf4f8-0d57-4bdd-94e3-633dd6cca562

import Theorems.Thm_mme_released_interior_owner2_cell10_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell11_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell12_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell13_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell14_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell15_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell18_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell19_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell20_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell21_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell22_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell25_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell26_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell27_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell28_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell31_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell32_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell33_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell36_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell37_normalized_child_bounds
import Theorems.Thm_mme_released_interior_owner2_cell40_normalized_child_bounds
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- Every positive joint label of this owner has a complete normalized child
bound, with its exact sum in one common rational denominator. -/
theorem solution (s : Fin 45)
    (hpositive : 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), s))) :
    ∃ q : Cell 4 6 (ReleasedInterior.parent s) → ℝ,
      (∑ c, q c) = (((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41942202922321095216409160173411488138, 55960130524645848041729144030007329375, 65647119664028885739187161250492487485, 65561141918178575025106518558840061965, 55911060779175072638739972560088602993, 41942229840276194187240424885527586029, 0, 0, 55960116008167972097744141767264843274, 67269995189203565952594385435065836238, 69817223465743135600274336199034202668, 67320264647779763064833840933005378118, 55912728557053206956830846769538129445, 0, 0, 65642878157126730469486533654286247151, 69812984196591644396408922957861964311, 69809604332343921353704353515387213668, 65554343838049830432860660102271800685, 0, 0, 65505034393518965593151668133700246641, 67291973786764334143182478326204357785, 65502232500709234246493578982912517964, 0, 0, 55899957943366341347115027614833331768, 55900833868164715997538077449607996565, 0, 0, 41917199297663028575868802388431730717, 0, 0, 0, 0] : Fin 45 → ℕ) s : ℝ) / 2000000000000000000000000000000000000) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 s (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 2 s (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 2 s).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 2 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 2 s).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 2 s c.1 c.2 + ReleasedInterior.splitWeight 2 s c.1
            (complement (ReleasedInterior.parent_total s c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by
  fin_cases s
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (0 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (0 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (1 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (1 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (2 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (2 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (3 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (3 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (4 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (4 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (5 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (5 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (6 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (6 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (7 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (7 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (8 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (8 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (9 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (9 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell10_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41942202922321095216409160173411488138 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell11_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960130524645848041729144030007329375 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell12_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65647119664028885739187161250492487485 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell13_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65561141918178575025106518558840061965 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell14_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55911060779175072638739972560088602993 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell15_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41942229840276194187240424885527586029 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (16 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (16 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (17 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (17 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell18_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55960116008167972097744141767264843274 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell19_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67269995189203565952594385435065836238 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell20_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69817223465743135600274336199034202668 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell21_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67320264647779763064833840933005378118 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell22_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55912728557053206956830846769538129445 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (23 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (23 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (24 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (24 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell25_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65642878157126730469486533654286247151 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell26_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69812984196591644396408922957861964311 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell27_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (69809604332343921353704353515387213668 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell28_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65554343838049830432860660102271800685 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (29 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (29 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (30 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (30 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell31_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65505034393518965593151668133700246641 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell32_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (67291973786764334143182478326204357785 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell33_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (65502232500709234246493578982912517964 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (34 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (34 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (35 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (35 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell36_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55899957943366341347115027614833331768 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell37_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (55900833868164715997538077449607996565 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (38 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (38 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (39 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (39 : Fin 45))) at hpositive
    omega
  · obtain ⟨q, hs, hb, hi⟩ := mme_released_interior_owner2_cell40_normalized_child_bounds
    refine ⟨q, ?_, hb, hi⟩
    change (∑ c, q c) = (41917199297663028575868802388431730717 / 2000000000000000000000000000000000000 : ℝ)
    norm_num [hs]
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (41 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (41 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (42 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (42 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (43 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (43 : Fin 45))) at hpositive
    omega
  · have hz : ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (44 : Fin 45))) = 0 := by decide +kernel
    change 0 < ReleasedJointInterior.weight (finProdFinEquiv ((2 : Fin 6), (44 : Fin 45))) at hpositive
    omega


#print axioms solution
