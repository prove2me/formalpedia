-- Prove2me | solution 1 for mme_permutation_modewise_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:00:06.644576+00:00
-- url     : https://prove2.me/submissions/7d7c9ac0-8ca9-46dd-8b69-5d1766ea6e65

import Definitions.Def_mme_permutation

open MME PiTensorProduct
universe u
set_option autoImplicit false

/-- A modewise linear map follows its mode when the tensor is permuted. -/
theorem solution {K : Type u} [Field K] {d : ℕ}
    (e : Equiv.Perm (Fin d)) (X : TensorObj K d)
    (f : ∀ i, X.V i →ₗ[K] X.V i) :
    TensorObj.permObj e { X with t := PiTensorProduct.map f X.t } =
      { TensorObj.permObj e X with t :=
        (PiTensorProduct.map (fun i => f (e.symm i))
          (TensorObj.permObj e X).t) } := by
  have ht := PiTensorProduct.map_reindex (R := K) f e X.t
  unfold TensorObj.permObj
  congr 1
  exact ht.symm

#print axioms solution
