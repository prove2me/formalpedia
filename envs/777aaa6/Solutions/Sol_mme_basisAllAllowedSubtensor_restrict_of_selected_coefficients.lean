-- Prove2me | solution 1 for mme_basisAllAllowedSubtensor_restrict_of_selected_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:38:08.69806+00:00
-- url     : https://prove2.me/submissions/95f02afa-188c-47e3-9372-21c36bd999de

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.TensorObj Module PiTensorProduct
universe u
set_option autoImplicit false

/-- Selecting allowed basis coordinates realizes a tensor restriction whenever
all selected coefficients agree with those of the target tensor. -/
theorem solution
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I : Fin 3 → Type u} {J : Fin 3 → Type u}
    [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (allowed : ∀ i, I i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, allowed i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict S (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let f := fun i ↦ (c i).equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun j ↦ (b i).coord (e i j)))
  have hf (i : Fin 3) (x : T.V i) (j : J i) :
      (c i).repr (f i x) j = (b i).repr x (e i j) := by
    change (c i).coord j ((c i).equivFun.symm _) = _
    rw [Basis.coord_equivFun_symm]
    rfl
  have hmap (x : PiTensorProduct K T.V) (w : ∀ i, J i) :
      (Basis.piTensorProduct c).repr (PiTensorProduct.map f x) w =
        (Basis.piTensorProduct b).repr x (fun i ↦ e i (w i)) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod,
        Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply, hf]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T S b allowed f
  · apply (Basis.piTensorProduct c).repr.injective
    ext w
    exact (hmap T.t w).trans (hc w)
  · intro i x hx
    apply (c i).repr.injective
    ext j
    rw [hf]
    have hne : x ≠ e i j := fun h ↦ hx (h ▸ he i j)
    simp [hne]


#print axioms solution
