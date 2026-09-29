-- Prove2me | solution 1 for mme_tensor_basis_cartesian_projection_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:53:11.010791+00:00
-- url     : https://prove2.me/submissions/899a22ed-bc3b-45c9-9400-7d8478f1baed

import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME PiTensorProduct Module TensorProduct
universe u
set_option autoImplicit false

private theorem basis_cartesian_projection
    {K : Type u} [Field K] {V W : Type u}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ι κ : Type u} (b : Basis ι K V) (c : Basis κ K W)
    (P : ι → Prop) (Q : κ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred (fun w : ι × κ => P w.1 ∧ Q w.2)] :
    (b.tensorProduct c).constr K
        (fun w => if P w.1 ∧ Q w.2 then (b.tensorProduct c) w else 0) =
      TensorProduct.map
        (b.constr K (fun x => if P x then b x else 0))
        (c.constr K (fun y => if Q y then c y else 0)) := by
  apply (b.tensorProduct c).ext
  rintro ⟨x,y⟩
  rw [Basis.constr_basis, Basis.tensorProduct_apply, TensorProduct.map_tmul,
    Basis.constr_basis, Basis.constr_basis]
  by_cases hx : P x <;> by_cases hy : Q y <;> simp [hx, hy]

/-- A Cartesian basis mask in the third mode of a Kronecker product is
exactly the product of the two separate third-mode masks. -/
theorem solution
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
        { Y with t := PiTensorProduct.map g Y.t } := by
  intro f g Z h
  have hm : h = fun i => TensorProduct.map (f i) (g i) := by
    funext i
    fin_cases i
    · change LinearMap.id = TensorProduct.map LinearMap.id LinearMap.id
      ext x y
      rfl
    · change LinearMap.id = TensorProduct.map LinearMap.id LinearMap.id
      ext x y
      rfl
    · exact basis_cartesian_projection b c P Q
  have ht : PiTensorProduct.map h Z.t =
      interchange (PiTensorProduct.map f X.t) (PiTensorProduct.map g Y.t) := by
    rw [hm]
    exact TensorObj.TypeGrading.kronMap_interchange f g X.t Y.t
  change ({ V := Z.V, t := PiTensorProduct.map h Z.t } : TensorObj K 3) = _
  rw [ht]
  rfl

#print axioms solution
