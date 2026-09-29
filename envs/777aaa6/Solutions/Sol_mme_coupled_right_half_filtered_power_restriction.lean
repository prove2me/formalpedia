-- Prove2me | solution 1 for mme_coupled_right_half_filtered_power_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:11:05.494979+00:00
-- url     : https://prove2.me/submissions/6586152b-735c-4bc3-a751-53aafd6e1b05

import Theorems.Thm_mme_permutation_modewise_map_eq
import Theorems.Thm_mme_permuted_power_word_basis_transport
import Definitions.Def_mme_CW_coupled_value

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

private noncomputable def unrotateRightMap
    {K : Type u} [Field K] (T : TensorObj K 3) :
    ∀ i, (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
      (TensorObj.permObj cyclicPerm T)).V i →ₗ[K] T.V i
  | ⟨0, _⟩ => LinearMap.id
  | ⟨1, _⟩ => LinearMap.id
  | ⟨2, _⟩ => LinearMap.id

private theorem unrotateRight_tensor
    {K : Type u} [Field K] (T : TensorObj K 3) :
    PiTensorProduct.map (unrotateRightMap T)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (TensorObj.permObj cyclicPerm T)).t = T.t := by
  have hpure (v : ∀ i, T.V i) :
      PiTensorProduct.map (unrotateRightMap T)
        ((reindex K _ (cyclicPerm.trans cyclicPerm))
          ((reindex K T.V cyclicPerm) (tprod K v))) = tprod K v := by
    simp only [reindex_tprod, map_tprod]
    congr 1
    funext i
    fin_cases i <;> rfl
  change PiTensorProduct.map (unrotateRightMap T)
    ((reindex K _ (cyclicPerm.trans cyclicPerm))
      ((reindex K T.V cyclicPerm) T.t)) = T.t
  induction T.t using PiTensorProduct.induction_on with
  | smul_tprod a v => simp only [map_smul, hpure]
  | add x y hx hy => simp only [map_add, hx, hy]


private def coupledWordIndex (q : ℕ) : Fin 3 → Type u
  | ⟨0, _⟩ => ULift.{u} (Fin q ⊕ Fin q)
  | ⟨1, _⟩ => ULift.{u} (Fin q ⊕ Fin q)
  | ⟨2, _⟩ => ULift.{u} (Fin 2 ⊕ (Fin q × Fin q))

private noncomputable def coupledWordBasis
    {K : Type u} [Field K] (q : ℕ) :
    ∀ i, Basis (coupledWordIndex.{u} q i) K ((coupledObj K q).V i)
  | ⟨0, _⟩ => (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
  | ⟨1, _⟩ => (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
  | ⟨2, _⟩ => (Pi.basisFun K (Fin 2 ⊕ (Fin q × Fin q))).reindex Equiv.ulift.symm

private noncomputable def unrotateRightBasis
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) :
    ∀ i, Basis (ι i) K
      ((TensorObj.permObj cyclicPerm T).V ((cyclicPerm.trans cyclicPerm).symm i))
  | ⟨0, _⟩ => b 0
  | ⟨1, _⟩ => b 1
  | ⟨2, _⟩ => b 2

/-- Reorienting the right coupled half carries its third-mode word filter
exactly to the second mode of an unpermuted coupled power. -/
theorem solution
    {K : Type u} [Field K] (q n : ℕ)
    (keep : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) n → Prop) [DecidablePred keep] :
    let C := coupledObj K q
    let S := (TensorObj.permObj cyclicPerm C).kronPow n
    let T := C.kronPow n
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let bs := kronPowModeBasis (TensorObj.permObj cyclicPerm C) 2 b n
    let bt := kronPowModeBasis C 1 b n
    let fs : ∀ i, S.V i →ₗ[K] S.V i := Function.update (fun _ => LinearMap.id) 2
      (bs.constr K (fun w => if keep w then bs w else 0))
    let ft : ∀ i, T.V i →ₗ[K] T.V i := Function.update (fun _ => LinearMap.id) 1
      (bt.constr K (fun w => if keep w then bt w else 0))
    TensorObj.Restrict { T with t := PiTensorProduct.map ft T.t }
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) { S with t := PiTensorProduct.map fs S.t }) := by
  intro C S T b bs bt fs ft
  have hb : ∀ i a, unrotateRightMap C i
      (unrotateRightBasis C (coupledWordBasis q) i a) = coupledWordBasis q i a := by
    intro i a
    fin_cases i <;> rfl
  obtain ⟨F, hF, hword⟩ := mme_permuted_power_word_basis_transport (cyclicPerm.trans cyclicPerm)
    (unrotateRightMap C) (unrotateRight_tensor C)
    (unrotateRightBasis C (coupledWordBasis q)) (coupledWordBasis q) hb n
  have hword1 (w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) n) : F 1 (bs w) = bt w :=
    hword 1 w
  have hcomp : (fun i => (F i).comp (fs ((cyclicPerm.trans cyclicPerm).symm i))) =
      fun i => (ft i).comp (F i) := by
    funext i
    fin_cases i
    · change (F 0).comp LinearMap.id = LinearMap.id.comp (F 0)
      rfl
    · apply bs.ext
      intro w
      change F 1 ((bs.constr K (fun w => if keep w then bs w else 0)) (bs w)) =
        (bt.constr K (fun w => if keep w then bt w else 0)) (F 1 (bs w))
      rw [Basis.constr_basis, hword1, Basis.constr_basis]
      split_ifs
      · exact hword1 w
      · exact (F 1).map_zero
    · change (F 2).comp LinearMap.id = LinearMap.id.comp (F 2)
      rfl
  rw [mme_permutation_modewise_map_eq]
  refine ⟨F, ?_⟩
  change PiTensorProduct.map F
    (PiTensorProduct.map (fun i => fs ((cyclicPerm.trans cyclicPerm).symm i))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) S).t) = PiTensorProduct.map ft T.t
  change (PiTensorProduct.map F ∘ₗ
    PiTensorProduct.map (fun i => fs ((cyclicPerm.trans cyclicPerm).symm i)))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) S).t = _
  rw [← PiTensorProduct.map_comp, hcomp, PiTensorProduct.map_comp,
    LinearMap.comp_apply, hF]

#print axioms solution
