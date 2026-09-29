-- Prove2me | Definitions.Def_mme_released_joint_interior_position_data
-- name    : mme_released_joint_interior_position_data
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T09:44:53.066165+00:00
-- url     : https://prove2.me/theorems/a071df25-624f-4abc-915d-ba13a3676983
-- title:
--   Regrouping joint elementary coordinates by owner
-- statement:
--   An explicit equivalence regroups the elementary positions of all six joint regions by owner and parent label. An embedding selects one label while preserving child halves and elementary entries, proving that the selected physical coordinates are distinct.

import Definitions.Def_mme_released_joint_interior_frame

namespace MME.ReleasedJointInterior

/-- One elementary coordinate is a child occurrence and one of its two entries. -/
noncomputable def childFineEquiv (r : Fin 6) (k : ℕ) :
    Fin (blocks r k * 4) ≃ RecursiveYZ.Position (size r k) × Fin 2 :=
  (finCongr (positions_length r k).symm).trans
    (finProdFinEquiv.symm.trans ((positions r k).prodCongr (Equiv.refl (Fin 2))))

/-- Regroup all elementary positions by owner and parent label. Both child
halves and their elementary entries retain their original order. -/
noncomputable def jointFineEquiv (k : ℕ) :
    (Σ r : Fin 6, Fin (blocks r k * 4)) ≃
      (Σ j : Fin 270, RecursiveYZ.Position (fun r => size r k j) × Fin 2) where
  toFun p :=
    let c := childFineEquiv p.1 k p.2
    ⟨c.1.1, ⟨⟨p.1,c.1.2⟩,c.2⟩⟩
  invFun p :=
    ⟨p.2.1.1, (childFineEquiv p.2.1.1 k).symm (⟨p.1,p.2.1.2⟩,p.2.2)⟩
  left_inv := by
    rintro ⟨r,t⟩
    dsimp
    simp only [Sigma.eta, Prod.eta, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨j,⟨r,t,h⟩,q⟩
    exact congrArg (fun c : RecursiveYZ.Position (size r k) × Fin 2 =>
      (⟨c.1.1, ⟨⟨r,c.1.2⟩,c.2⟩⟩ :
        Σ j : Fin 270, RecursiveYZ.Position (fun r => size r k j) × Fin 2))
      ((childFineEquiv r k).apply_symm_apply (⟨j,t,h⟩,q))

/-- Select one owner's parent label from the regrouped elementary coordinates.
The embedding proves that no physical coordinate is repeated. -/
noncomputable def ownerFineEmbedding (k : ℕ) (j : Fin 270) {L N : ℕ}
    (e : Fin L ≃ RecursiveYZ.Position (fun r => size r k j))
    (length : L * 2 ^ (2 - 1) = N) :
    Fin N ↪ (Σ r : Fin 6, Fin (blocks r k * 4)) :=
  ((finCongr length.symm).trans
    (finProdFinEquiv.symm.trans (e.prodCongr (Equiv.refl (Fin 2))))).toEmbedding.trans
    ((⟨fun p => ⟨j,p⟩, by intro a b h; cases h; rfl⟩ :
      (RecursiveYZ.Position (fun r => size r k j) × Fin 2) ↪
        (Σ j : Fin 270, RecursiveYZ.Position (fun r => size r k j) × Fin 2)).trans
      (jointFineEquiv k).symm.toEmbedding)

end MME.ReleasedJointInterior


