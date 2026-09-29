-- Prove2me | solution 1 for mme_basis_preserving_restriction_mask_descent
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:03:03.593739+00:00
-- url     : https://prove2.me/submissions/ae207704-09c5-4c5a-8a8d-43a201cfe225

import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.Basis.Defs

open MME Module PiTensorProduct
universe u
set_option autoImplicit false

/-- A basis-preserving tensor restriction descends through any common family
of coordinate masks, including non-Cartesian predicates on word indices. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (F : ∀ i, X.V i →ₗ[K] Y.V i)
    (hF : PiTensorProduct.map F X.t = Y.t)
    {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (X.V i)) (c : ∀ i, Basis (ι i) K (Y.V i))
    (hb : ∀ i a, F i (b i a) = c i a)
    (keep : ∀ i, ι i → Prop) [∀ i, DecidablePred (keep i)] :
    let p : ∀ i, X.V i →ₗ[K] X.V i :=
      fun i => (b i).constr K (fun a => if keep i a then b i a else 0)
    let q : ∀ i, Y.V i →ₗ[K] Y.V i :=
      fun i => (c i).constr K (fun a => if keep i a then c i a else 0)
    TensorObj.Restrict { Y with t := PiTensorProduct.map q Y.t }
      { X with t := PiTensorProduct.map p X.t } := by
  intro p q
  have hcomp : (fun i => (F i).comp (p i)) = fun i => (q i).comp (F i) := by
    funext i
    apply (b i).ext
    intro a
    simp only [LinearMap.comp_apply]
    change F i (((b i).constr K (fun a => if keep i a then b i a else 0)) (b i a)) =
      ((c i).constr K (fun a => if keep i a then c i a else 0)) (F i (b i a))
    rw [Basis.constr_basis, hb, Basis.constr_basis]
    split_ifs <;> simp [hb]
  refine ⟨F, ?_⟩
  change PiTensorProduct.map F (PiTensorProduct.map p X.t) =
    PiTensorProduct.map q Y.t
  change (PiTensorProduct.map F ∘ₗ PiTensorProduct.map p) X.t = _
  rw [← PiTensorProduct.map_comp, hcomp, PiTensorProduct.map_comp,
    LinearMap.comp_apply, hF]

#print axioms solution
