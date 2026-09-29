-- Prove2me | Theorems.Thm_mme_profiled_CW_regroup_product_restrict
-- name    : mme_profiled_CW_regroup_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:50:47.148688+00:00
-- url     : https://prove2.me/theorems/a3576247-4a85-4e75-a874-875eb1e1e94c
-- title:
--   Coordinate regrouping gives a product tensor restriction
-- statement:
--   A bijection between two partitions of elementary CW coordinates gives a restriction from the target region product to the source part product whenever the target predicates imply the source predicates in a common tensor mode. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_profiled_CW_joint_projection_restrict
open MME MME.TensorObj MME.ProfiledCW
universe u

theorem mme_profiled_CW_regroup_product_restrict {K : Type u} [Field K]
    {a b : ℕ} (sizeA : Fin a → ℕ) (sizeB : Fin b → ℕ)
    (e : (Σ j : Fin a, Fin (sizeA j)) ≃ (Σ r : Fin b, Fin (sizeB r)))
    (P : ∀ j, Predicate (sizeA j)) (Q : ∀ r, Predicate (sizeB r))
    (inside : ∀ i (x : ∀ r, FineWord (sizeB r)),
      (∀ r, Q r i (x r)) →
        ∀ j, P j i (fun q => x (e ⟨j,q⟩).1 (e ⟨j,q⟩).2)) :
    Restrict (kronFin b (fun r => tensor K (Q r)))
      (kronFin a (fun j => tensor K (P j))) := by sorry
