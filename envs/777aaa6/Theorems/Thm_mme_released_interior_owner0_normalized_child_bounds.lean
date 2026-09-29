-- Prove2me | Theorems.Thm_mme_released_interior_owner0_normalized_child_bounds
-- name    : mme_released_interior_owner0_normalized_child_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T08:49:57.849263+00:00
-- url     : https://prove2.me/theorems/21420a6e-171d-4ec0-a2f7-08a575b7a2df
-- title:
--   Owner 0 has complete actual child tables
-- statement:
--   Every positive parent label has an exact normalized child table bounding all permitted boundary and interior modes, including zero-mass regions. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

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

theorem mme_released_interior_owner0_normalized_child_bounds (s : Fin 45)
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
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by sorry
