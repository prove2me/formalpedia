-- Prove2me | solution 1 for mme_released_joint_interior_owner_fine_partition
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:58:34.037582+00:00
-- url     : https://prove2.me/submissions/80ae0a11-1b27-49f5-8851-bed91dc739bb

import Definitions.Def_mme_released_joint_interior_position_data

open MME MME.RecursiveYZ MME.ReleasedJointInterior

/-- The owner embeddings together partition all elementary joint coordinates.
This includes labels of size zero and requires no positivity assumption. -/
theorem solution
    (k : ℕ) (L N : Fin 270 → ℕ)
    (e : ∀ j, Fin (L j) ≃ Position (fun r => size r k j))
    (length : ∀ j, L j * 2 ^ (2 - 1) = N j) :
    ∃ E : (Σ j : Fin 270, Fin (N j)) ≃
        (Σ r : Fin 6, Fin (blocks r k * 4)),
      ∀ j q, E ⟨j,q⟩ = ownerFineEmbedding k j (e j) (length j) q := by
  let E := (Equiv.sigmaCongrRight (fun j =>
    (finCongr (length j).symm).trans
      (finProdFinEquiv.symm.trans ((e j).prodCongr (Equiv.refl (Fin 2)))))).trans
        (jointFineEquiv k).symm
  exact ⟨E, fun _ _ => rfl⟩


#print axioms solution
