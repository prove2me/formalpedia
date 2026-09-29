-- Prove2me | Definitions.Def_mme_TypeGrading_permutation
-- name    : mme_TypeGrading_permutation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T02:57:54.522132+00:00
-- url     : https://prove2.me/theorems/24bcfa40-bf70-4ab1-8a0f-44b7bcbc0fd3
-- title:
--   Relabel tensor type gradings under mode permutations
-- statement:
--   A permutation of an order-$d$ tensor's modes relabels any finite type grading by sending the class in new mode $i$ to the old class in mode $e^{-1}(i)$. The module proves the exact compatibility of block projections with tensor reindexing and shows that every relabeled block subtensor is isomorphic to the corresponding mode permutation of the original block.
--
--   This is the permutation-specific grading transport needed when forming cyclic symmetrizations in C-tensor and laser-method arguments.
-- source:
--   Functoriality of tensor products and internal direct sums under permutation of tensor modes.

import Definitions.Def_mme_permutation
import Definitions.Def_mme_block_subtensor

open MME PiTensorProduct

universe u

namespace MME.TensorObj.TypeGrading

variable {K : Type u} [Field K] {d t : ℕ}
variable {T : TensorObj K d}

def permObjGrading (G : T.TypeGrading t) (e : Equiv.Perm (Fin d)) :
    (TensorObj.permObj e T).TypeGrading t where
  decomp i := G.decomp (e.symm i)
  is_internal i := G.is_internal (e.symm i)

theorem permObjGrading_blockTensor
    (G : T.TypeGrading t) (e : Equiv.Perm (Fin d))
    (rho : Fin d → Fin t) :
    (permObjGrading G e).blockTensor (fun i ↦ rho (e.symm i)) =
      (PiTensorProduct.reindex K
          (fun j ↦ G.classOf j (rho j)) e)
        (G.blockTensor rho) := by
  unfold TensorObj.TypeGrading.blockTensor
  change
    (PiTensorProduct.map
      (fun i ↦ G.blockProj (e.symm i) (rho (e.symm i)))
      ((PiTensorProduct.reindex K T.V e) T.t)) = _
  exact PiTensorProduct.map_reindex
    (fun j ↦ G.blockProj j (rho j)) e T.t

theorem permObjGrading_blockSubtensor_iso
    (G : T.TypeGrading t) (e : Equiv.Perm (Fin d))
    (rho : Fin d → Fin t) :
    TensorObj.Isomorphic
      ((permObjGrading G e).blockSubtensor
        (fun i ↦ rho (e.symm i)))
      (TensorObj.permObj e (G.blockSubtensor rho)) := by
  have ht := permObjGrading_blockTensor G e rho
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := fun i ↦ G.classOf (e.symm i) (rho (e.symm i))))
      (TensorObj.permObj e (G.blockSubtensor rho)).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := fun i ↦ G.classOf (e.symm i) (rho (e.symm i))))
      ((permObjGrading G e).blockSubtensor
        (fun i ↦ rho (e.symm i))).t
    exact hmap.trans ht

end MME.TensorObj.TypeGrading


