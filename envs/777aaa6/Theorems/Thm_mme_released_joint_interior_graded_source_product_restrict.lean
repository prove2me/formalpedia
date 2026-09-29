-- Prove2me | Theorems.Thm_mme_released_joint_interior_graded_source_product_restrict
-- name    : mme_released_joint_interior_graded_source_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:34:46.607225+00:00
-- url     : https://prove2.me/theorems/61d326f9-2083-4ede-9120-ad32ae61ff23
-- title:
--   All graded joint addresses restrict the owner window product
-- statement:
--   The six joint source windows, retaining all addresses with the prescribed split histograms, form an actual tensor restriction of the released interior owner-window product. A fixed reference address is not assumed. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_graded_source
import Theorems.Thm_mme_released_joint_interior_common_mode_window
import Theorems.Thm_mme_released_joint_interior_owner_fine_partition
import Theorems.Thm_mme_released_joint_interior_owner_mass
import Theorems.Thm_mme_profiled_CW_regroup_product_restrict
open scoped BigOperators
open MME MME.TensorObj MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

theorem mme_released_joint_interior_graded_source_product_restrict
    {K : Type u} [Field K] (k : ℕ) (hk : 0 < k)
    (eps : ℝ) :
    let P : ∀ j : Fin 270,
        ProfiledCW.Predicate ((k * weight j * denominator ^ 4) * 4) :=
      fun j i z => 0 < weight j →
        (∀ p : Fin (k * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1
                ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps
    let Q : ∀ r : Fin 6, ProfiledCW.Predicate (blocks r k * 4) :=
      fun r i x => gradedSource r k eps ((roleEquiv r).symm i) x
    Restrict (kronFin 6 (fun r => ProfiledCW.tensor K (Q r)))
      (kronFin 270 (fun j => ProfiledCW.tensor K (P j))) := by sorry
