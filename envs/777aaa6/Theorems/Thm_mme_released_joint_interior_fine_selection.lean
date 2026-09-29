-- Prove2me | Theorems.Thm_mme_released_joint_interior_fine_selection
-- name    : mme_released_joint_interior_fine_selection
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:48:43.796443+00:00
-- url     : https://prove2.me/theorems/cdc6a5ae-7870-4e72-a534-412be10de951
-- title:
--   Physical coordinate selection preserves joint child words
-- statement:
--   Splitting a word selected by the explicit owner embedding agrees with the original joint child words at both elementary entries. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_position_data
open MME MME.RecursiveYZ MME.CompleteSplit MME.ReleasedJointInterior

theorem mme_released_joint_interior_fine_selection
    (k : ℕ) (j : Fin 270) {L N : ℕ}
    (e : Fin L ≃ Position (fun r => size r k j))
    (length : L * 2 ^ (2 - 1) = N)
    (x : ∀ r : Fin 6, ProfiledCW.FineWord (blocks r k * 4))
    (p : Position (fun r => size r k j)) :
    ProfiledCW.split e length
      (fun q => x (ownerFineEmbedding k j e length q).1
        (ownerFineEmbedding k j e length q).2) p =
      ProfiledCW.split (positions p.1 k) (positions_length p.1 k) (x p.1) ⟨j,p.2⟩ := by sorry
