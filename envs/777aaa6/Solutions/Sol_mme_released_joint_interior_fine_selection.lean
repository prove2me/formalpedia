-- Prove2me | solution 1 for mme_released_joint_interior_fine_selection
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:49:17.770268+00:00
-- url     : https://prove2.me/submissions/3c8a8c6e-873e-4efb-bddf-ed18a189ab34

import Definitions.Def_mme_released_joint_interior_position_data

open MME MME.RecursiveYZ MME.CompleteSplit MME.ReleasedJointInterior

/-- Reading an owner label through its physical coordinate embedding agrees
with splitting the original joint words. Both square-child entries are preserved. -/
theorem solution
    (k : ℕ) (j : Fin 270) {L N : ℕ}
    (e : Fin L ≃ Position (fun r => size r k j))
    (length : L * 2 ^ (2 - 1) = N)
    (x : ∀ r : Fin 6, ProfiledCW.FineWord (blocks r k * 4))
    (p : Position (fun r => size r k j)) :
    ProfiledCW.split e length
      (fun q => x (ownerFineEmbedding k j e length q).1
        (ownerFineEmbedding k j e length q).2) p =
      ProfiledCW.split (positions p.1 k) (positions_length p.1 k) (x p.1) ⟨j,p.2⟩ := by
  funext h
  simp only [ProfiledCW.split, ownerFineEmbedding, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Equiv.trans_apply, finCongr_apply,
    Equiv.prodCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  have hp := (finProdFinEquiv : Fin L × Fin 2 ≃ Fin (L * 2)).symm_apply_apply
    (e.symm p, h)
  rw [hp]
  simp only [Prod.map_apply]
  rw [e.apply_symm_apply p]
  change x p.1 ((childFineEquiv p.1 k).symm (⟨j,p.2⟩,h)) = _
  simp only [childFineEquiv, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_symm, finCongr_symm, finCongr_apply]
  rfl


#print axioms solution
