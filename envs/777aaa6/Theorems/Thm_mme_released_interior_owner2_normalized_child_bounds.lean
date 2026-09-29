-- Prove2me | Theorems.Thm_mme_released_interior_owner2_normalized_child_bounds
-- name    : mme_released_interior_owner2_normalized_child_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T17:01:08.612979+00:00
-- url     : https://prove2.me/theorems/af1e1e2e-dd6d-4a5f-aa3b-2ba86618d7ff
-- title:
--   Owner 2 has complete actual child tables
-- statement:
--   Every positive parent label has an exact normalized child table bounding all permitted boundary and interior modes, including zero-mass regions. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

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

theorem mme_released_interior_owner2_normalized_child_bounds (s : Fin 45)
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
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by sorry
