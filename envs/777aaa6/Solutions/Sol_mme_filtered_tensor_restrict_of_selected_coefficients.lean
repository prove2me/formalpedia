-- Prove2me | solution 1 for mme_filtered_tensor_restrict_of_selected_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:45:03.270315+00:00
-- url     : https://prove2.me/submissions/39e073fd-519d-416e-82a5-035ddefe334f

import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.TensorObj Module PiTensorProduct
open scoped Classical
universe u
set_option autoImplicit false

private theorem projection_on_basis
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) (i : Fin 3) (j : ι i) :
    let G := T.basisAllAllowedGrading b allowed
    (G.classOf i 0).subtype (G.blockProj i 0 (b i j)) =
      if allowed i j then b i j else 0 := by
  classical
  dsimp only
  let G := T.basisAllAllowedGrading b allowed
  by_cases hj : allowed i j
  · rw [if_pos hj]
    have hx : b i j ∈ G.classOf i 0 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 0
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_pos hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = b i j
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)
  · rw [if_neg hj]
    have hx : b i j ∈ G.classOf i 1 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = 0
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
        (show (1 : Fin 2) ≠ 0 by decide) hx)

/-- Coordinate selection descends through source and target profile filters. -/
theorem solution
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I J : Fin 3 → Type u} [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (P : ∀ i, I i → Prop) (Q : ∀ i, J i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, Q i j → P i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict (S.basisAllAllowedSubtensor c Q) (T.basisAllAllowedSubtensor b P) := by
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
  have ht : PiTensorProduct.map f T.t = S.t := by
    apply (Basis.piTensorProduct c).repr.injective
    ext w
    exact (hmap T.t w).trans (hc w)
  let G := S.basisAllAllowedGrading c Q
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T
    (S.basisAllAllowedSubtensor c Q) b P (fun i ↦ (G.blockProj i 0).comp (f i))
  · change PiTensorProduct.map (fun i ↦ (G.blockProj i 0).comp (f i)) T.t =
      PiTensorProduct.map (fun i ↦ G.blockProj i 0) S.t
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, ht]
  · intro i x hx
    change G.blockProj i 0 (f i (b i x)) = 0
    rw [← (c i).sum_repr (f i (b i x))]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : Q i j
    · have hne : x ≠ e i j := fun h ↦ hx (h ▸ he i j hj)
      rw [hf]
      simp [hne]
    · have hz : G.blockProj i 0 (c i j) = 0 := by
        apply Subtype.val_injective
        change (G.classOf i 0).subtype (G.blockProj i 0 (c i j)) = 0
        rw [projection_on_basis, if_neg hj]
      rw [hz, smul_zero]


#print axioms solution
