-- Prove2me | solution 1 for mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:23:31.067595+00:00
-- url     : https://prove2.me/submissions/0f40cc28-b65f-4e4d-801c-e537a0d2767f

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Mathlib.LinearAlgebra.TensorProduct.Associator

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support
open Module PiTensorProduct TensorProduct BigOperators
universe u
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace MME.DWZBalancedFourth
variable {K : Type u} [Field K] {d : ℕ}

private theorem interchange_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_naturality {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V₁ V₂ V₃ V₄ : ι → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (a : PiTensorProduct K V₁) (b : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i)) (interchange a b) =
    interchange (PiTensorProduct.map f a) (PiTensorProduct.map g b) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_pure, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_pure]
      simp only [TensorProduct.map_tmul]
    | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
  | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]

private theorem interchange_right_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (a : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => (TensorProduct.rid K (V i)).toLinearMap)
      (interchange a (tprod K (fun _ => (1 : K)))) = a := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, LinearMap.smul_apply]
    rw [interchange_pure, PiTensorProduct.map_tprod]
    simp only [LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul]
  | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]

private theorem interchange_assoc_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) (c : PiTensorProduct K U) :
    PiTensorProduct.map (fun i => (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap)
      (interchange a (interchange b c)) = interchange (interchange a b) c := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [interchange_pure, interchange_pure, PiTensorProduct.map_tprod,
          interchange_pure, interchange_pure]
        simp only [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, mul_assoc]
      | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 => simp only [LinearMap.add_apply, map_add, ih1, ih2]

noncomputable def balancedEquiv (T : TensorObj K d) (i : Fin d) :
    (T.kronPow 4).V i ≃ₗ[K] ((T.kron T).kron (T.kron T)).V i :=
  (TensorProduct.congr (LinearEquiv.refl K (T.V i))
    (TensorProduct.congr (LinearEquiv.refl K (T.V i))
      (TensorProduct.congr (LinearEquiv.refl K (T.V i))
        (TensorProduct.rid K (T.V i))))).trans
    (TensorProduct.assoc K (T.V i) (T.V i) (T.V i ⊗[K] T.V i)).symm

theorem balancedEquiv_tensor (T : TensorObj K d) :
    PiTensorProduct.map (fun i => (balancedEquiv T i).toLinearMap) (T.kronPow 4).t =
      ((T.kron T).kron (T.kron T)).t := by
  have hdrop :
      PiTensorProduct.map (fun i =>
        TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
          (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
            (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
              (TensorProduct.rid K (T.V i)).toLinearMap)))
        (T.kronPow 4).t =
        interchange T.t (interchange T.t (interchange T.t T.t)) := by
    change PiTensorProduct.map _ (interchange T.t (interchange T.t
      (interchange T.t (interchange T.t (tprod K (fun _ => (1 : K))))))) = _
    rw [interchange_naturality, interchange_naturality, interchange_naturality,
      interchange_right_one]
    simp only [PiTensorProduct.map_id, LinearMap.id_coe, id_eq]
  change PiTensorProduct.map (fun i =>
    (TensorProduct.assoc K (T.V i) (T.V i) (T.V i ⊗[K] T.V i)).symm.toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
        (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
          (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i)
            (TensorProduct.rid K (T.V i)).toLinearMap))) _ = _
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hdrop]
  exact interchange_assoc_symm T.t T.t (interchange T.t T.t)

private theorem word_basis_zero (T : TensorObj K d) (i : Fin d)
    {I : Type u} (b : Basis I K (T.V i)) (w : Fin 0 → I) :
    kronPowModeWordBasis T i b 0 w = (1 : K) :=
  Basis.singleton_apply (Fin 0 → I) K w

private theorem word_basis_succ (T : TensorObj K d) (i : Fin d)
    {I : Type u} (b : Basis I K (T.V i)) (n : ℕ) (w : Fin (n + 1) → I) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (Fin.tail w) := by
  letI : IsScalarTower K K (T.V i) := IsScalarTower.of_algebraMap_smul (by simp)
  exact (Basis.reindex_apply
    (b.tensorProduct (kronPowModeWordBasis T i b n))
    (Fin.consEquiv (fun _ : Fin (n + 1) => I)) w).trans
      (Basis.tensorProduct_apply b (kronPowModeWordBasis T i b n) (w 0) (Fin.tail w))

theorem balancedEquiv_basis (T : TensorObj K d) (i : Fin d)
    {I : Type u} (b : Basis I K (T.V i)) (w : Fin 4 → I) :
    balancedEquiv T i (kronPowModeWordBasis T i b 4 w) =
      (b (w 0) ⊗ₜ[K] b (w 1)) ⊗ₜ[K] (b (w 2) ⊗ₜ[K] b (w 3)) := by
  have hw : kronPowModeWordBasis T i b 4 w =
      b (w 0) ⊗ₜ[K] (b (w 1) ⊗ₜ[K]
        (b (w 2) ⊗ₜ[K] (b (w 3) ⊗ₜ[K] (1 : K)))) := by
    rw [word_basis_succ, word_basis_succ, word_basis_succ, word_basis_succ]
    rw [word_basis_zero]
    rfl
  rw [hw]
  change (b (w 0) ⊗ₜ[K] b (w 1)) ⊗ₜ[K]
      (b (w 2) ⊗ₜ[K] ((TensorProduct.rid K (T.V i)) (b (w 3) ⊗ₜ[K] (1 : K)))) = _
  exact congrArg (fun z : T.V i =>
    (b (w 0) ⊗ₜ[K] b (w 1)) ⊗ₜ[K] (b (w 2) ⊗ₜ[K] z))
    ((TensorProduct.rid_tmul (R := K) (b (w 3)) (1 : K)).trans (one_smul K (b (w 3))))

private theorem canonical_square_pair (q : ℕ) (i : Fin 3) (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q i (a, b) =
      cwThreeCanonicalBasis K q i a ⊗ₜ[K] cwThreeCanonicalBasis K q i b := by
  fin_cases i <;>
    exact Basis.tensorProduct_apply (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2))) a b

theorem cwFourth_preserves_tensor_and_basis (q : ℕ) :
    ∃ Φ : ∀ i, ((CWObj K q).kronPow 4).V i ≃ₗ[K] (cwFourthObj K q).V i,
      PiTensorProduct.map (fun i => (Φ i).toLinearMap) ((CWObj K q).kronPow 4).t =
        (cwFourthObj K q).t ∧
      ∀ i (w : Fin 4 → ULift.{u} (Fin (q + 2))),
        Φ i (kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) 4 w) =
        cwFourthCanonicalBasis K q i
          (((w 0).down, (w 1).down), ((w 2).down, (w 3).down)) := by
  refine ⟨balancedEquiv (CWObj K q), balancedEquiv_tensor (CWObj K q), ?_⟩
  intro i w
  calc
    _ = ((((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (w 0)) ⊗ₜ[K]
        (((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (w 1))) ⊗ₜ[K]
        ((((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (w 2)) ⊗ₜ[K]
        (((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (w 3))) :=
      balancedEquiv_basis (CWObj K q) i
        ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) w
    _ = (cwThreeCanonicalBasis K q i (w 0).down ⊗ₜ[K]
        cwThreeCanonicalBasis K q i (w 1).down) ⊗ₜ[K]
        (cwThreeCanonicalBasis K q i (w 2).down ⊗ₜ[K]
        cwThreeCanonicalBasis K q i (w 3).down) := by
      simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply]
    _ = cwSquareCanonicalBasis K q i ((w 0).down, (w 1).down) ⊗ₜ[K]
        cwSquareCanonicalBasis K q i ((w 2).down, (w 3).down) := by
      rw [canonical_square_pair, canonical_square_pair]
    _ = _ := (Basis.tensorProduct_apply (cwSquareCanonicalBasis K q i)
      (cwSquareCanonicalBasis K q i) ((w 0).down, (w 1).down)
        ((w 2).down, (w 3).down)).symm

theorem cwFourth_word_grades (q : ℕ) (w : Fin 4 → ULift.{u} (Fin (q + 2))) :
    (cwFourthPairGrade q
      (((w 0).down, (w 1).down), ((w 2).down, (w 3).down))).val =
      ∑ r : Fin 4, (cwSquareCoordGrade q (w r).down).val ∧
    (cwSquarePairGrade q ((w 0).down, (w 1).down)).val =
      ∑ r : Fin 2, (cwSquareCoordGrade q (w (Fin.castAdd 2 r)).down).val := by
  constructor <;>
    simp [cwFourthPairGrade, cwSquarePairGrade, Fin.sum_univ_succ, Nat.add_assoc]

end MME.DWZBalancedFourth

open MME.DWZBalancedFourth

theorem solution {K : Type u} [Field K] (q : ℕ) :
    ∃ Φ : ∀ i, ((CWObj K q).kronPow 4).V i ≃ₗ[K] (cwFourthObj K q).V i,
      PiTensorProduct.map (fun i => (Φ i).toLinearMap) ((CWObj K q).kronPow 4).t =
        (cwFourthObj K q).t ∧
      (∀ i (w : Fin 4 → ULift.{u} (Fin (q + 2))),
        Φ i (kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) 4 w) =
        cwFourthCanonicalBasis K q i
          (((w 0).down, (w 1).down), ((w 2).down, (w 3).down))) ∧
      ∀ w : Fin 4 → ULift.{u} (Fin (q + 2)),
        (cwFourthPairGrade q
          (((w 0).down, (w 1).down), ((w 2).down, (w 3).down))).val =
          ∑ r : Fin 4, (cwSquareCoordGrade q (w r).down).val ∧
        (cwSquarePairGrade q ((w 0).down, (w 1).down)).val =
          ∑ r : Fin 2, (cwSquareCoordGrade q (w (Fin.castAdd 2 r)).down).val := by
  obtain ⟨Φ, ht, hb⟩ := cwFourth_preserves_tensor_and_basis (K := K) q
  exact ⟨Φ, ht, hb, cwFourth_word_grades q⟩


