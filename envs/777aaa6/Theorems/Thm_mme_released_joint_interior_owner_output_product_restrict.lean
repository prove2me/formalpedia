-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_output_product_restrict
-- name    : mme_released_joint_interior_owner_output_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:56:23.44746+00:00
-- url     : https://prove2.me/theorems/714d3cf7-3c48-49eb-a212-1415feb35163
-- title:
--   Exact owner outputs restrict the joint output product
-- statement:
--   Physical coordinate regrouping gives an actual tensor restriction from the exact joint output product to the product of exact owner outputs. This is the direction needed to perform owner child extraction after joint parent hashing. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_common_mode_graded_iff
import Theorems.Thm_mme_released_joint_interior_common_mode_useful_iff
import Theorems.Thm_mme_released_joint_interior_owner_fine_partition
import Theorems.Thm_mme_released_joint_interior_fine_selection
import Theorems.Thm_mme_profiled_CW_regroup_product_restrict
open MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior
universe u

theorem mme_released_joint_interior_owner_output_product_restrict
    {K : Type u} [Field K] (k : ℕ)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (L N : Fin 270 → ℕ)
    (e : ∀ j, Fin (L j) ≃ Position (fun r => size r k j))
    (length : ∀ j, L j * 2 ^ (2 - 1) = N j) :
    Restrict
      (kronFin 270 (fun j => ProfiledCW.tensor K (fun i x =>
        Graded (ReleasedInterior.parent_total (component j).2)
          ((roleEquiv (component j).1).symm i)
          (fun r t => (splitEquiv r j).symm (a r j t))
          (ProfiledCW.split (e j) (length j) x) ∧
        Useful (fullCell (ReleasedInterior.parent_total (component j).2)
          (fun r t => (splitEquiv r j).symm (a r j t)))
          (fun c w => k * weight j * ReleasedInterior.integerProfile
            (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
          (ProfiledCW.split (e j) (length j) x))))
      (kronFin 6 (fun r => ProfiledCW.tensor K (fun i x =>
        Graded (parent_total r) ((roleEquiv r).symm i) (a r)
          (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
        Useful (fullCell (parent_total r) (a r))
          (integerProfile r k ((roleEquiv r).symm i))
          (ProfiledCW.split (positions r k) (positions_length r k) x)))) := by sorry
