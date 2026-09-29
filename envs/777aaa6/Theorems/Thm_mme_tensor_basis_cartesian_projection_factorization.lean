-- Prove2me | Theorems.Thm_mme_tensor_basis_cartesian_projection_factorization
-- name    : mme_tensor_basis_cartesian_projection_factorization
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:53:02.722654+00:00
-- url     : https://prove2.me/theorems/7752e13c-24c5-49ab-9f95-df7e1dee9502
-- title:
--   Cartesian basis projection factors across a Kronecker product
-- statement:
--   Let X and Y be order-three tensors over a field, with bases b and c in their third modes. For any predicates P and Q on the respective basis indices, project the third mode of X tensor Y onto basis pairs satisfying P and Q. The resulting tensor equals the Kronecker product of X projected onto P and Y projected onto Q, with the other modes unchanged.
-- source:
--   Tensor quotient permutation identities and tensor-product basis naturality.

import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME PiTensorProduct Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_tensor_basis_cartesian_projection_factorization
    {K : Type u} [Field K] (X Y : TensorObj K 3)
    {ι κ : Type u} (b : Basis ι K (X.V 2)) (c : Basis κ K (Y.V 2))
    (P : ι → Prop) (Q : κ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred (fun w : ι × κ => P w.1 ∧ Q w.2)] :
    let f : ∀ i, X.V i →ₗ[K] X.V i :=
      Function.update (fun _ => LinearMap.id) 2
        (b.constr K (fun x => if P x then b x else 0))
    let g : ∀ i, Y.V i →ₗ[K] Y.V i :=
      Function.update (fun _ => LinearMap.id) 2
        (c.constr K (fun y => if Q y then c y else 0))
    let Z := TensorObj.kron X Y
    let h : ∀ i, Z.V i →ₗ[K] Z.V i :=
      Function.update (fun _ => LinearMap.id) 2
        ((b.tensorProduct c).constr K
          (fun w => if P w.1 ∧ Q w.2 then (b.tensorProduct c) w else 0))
    ({ Z with t := PiTensorProduct.map h Z.t } : TensorObj K 3) =
      TensorObj.kron
        { X with t := PiTensorProduct.map f X.t }
        { Y with t := PiTensorProduct.map g Y.t } := by sorry
