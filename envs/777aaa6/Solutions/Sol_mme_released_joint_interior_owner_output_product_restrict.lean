-- Prove2me | solution 1 for mme_released_joint_interior_owner_output_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:32.923129+00:00
-- url     : https://prove2.me/submissions/672b6220-5f9a-4e29-ab0d-378d186c6b70

import Theorems.Thm_mme_released_joint_interior_common_mode_graded_iff
import Theorems.Thm_mme_released_joint_interior_common_mode_useful_iff
import Theorems.Thm_mme_released_joint_interior_owner_fine_partition
import Theorems.Thm_mme_released_joint_interior_fine_selection
import Theorems.Thm_mme_profiled_CW_regroup_product_restrict

open MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior
universe u

/-- The exact owner outputs restrict the exact joint output product after
physical coordinate regrouping. This direction permits child extraction after
joint parent hashing, without replacing its aggregate copy count. -/
theorem solution
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
          (ProfiledCW.split (positions r k) (positions_length r k) x)))) := by
  obtain ⟨E, hE⟩ := mme_released_joint_interior_owner_fine_partition k L N e length
  apply mme_profiled_CW_regroup_product_restrict (fun r => blocks r k * 4) N E.symm
  intro i x hx
  let y : ∀ r : Fin 6, ProfiledCW.FineWord (blocks r k * 4) :=
    fun r q => x (E.symm ⟨r,q⟩).1 (E.symm ⟨r,q⟩).2
  let f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2 :=
    fun r => ProfiledCW.split (positions r k) (positions_length r k) (y r)
  have hselected (j : Fin 270) :
      (fun p => f p.1 ⟨j,p.2⟩) = ProfiledCW.split (e j) (length j) (x j) := by
    funext p
    dsimp only [f]
    rw [← mme_released_joint_interior_fine_selection k j (e j) (length j) y p]
    have hxj : (fun q => y (ownerFineEmbedding k j (e j) (length j) q).1
        (ownerFineEmbedding k j (e j) (length j) q).2) = x j := by
      funext q
      change x (E.symm (ownerFineEmbedding k j (e j) (length j) q)).1
        (E.symm (ownerFineEmbedding k j (e j) (length j) q)).2 = x j q
      rw [← hE j q, E.symm_apply_apply]
    rw [hxj]
  have hg := (mme_released_joint_interior_common_mode_graded_iff k i a f).mpr
    (fun j => by rw [hselected j]; exact (hx j).1)
  have hu := (mme_released_joint_interior_common_mode_useful_iff k i a f).mpr
    (fun j => by rw [hselected j]; exact (hx j).2)
  intro r
  exact ⟨hg r, hu r⟩


#print axioms solution
