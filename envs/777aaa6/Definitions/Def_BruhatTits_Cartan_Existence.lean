-- Prove2me | Definitions.Def_BruhatTits_Cartan_Existence
-- name    : BruhatTits_Cartan_Existence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:08:44.504737+00:00
-- url     : https://prove2.me/theorems/a0768f6c-a1b9-441c-beef-3c53a54b7a97
-- title:
--   Existence
-- statement:
--   Definitions and structural lemmas for Existence, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Existence.lean

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_coeffs_sup_le
import Theorems.Thm_Matrix_coeffs_sup_transpose
import Theorems.Thm_Matrix_map_listProd_toGL
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
local notation "v" => ValuationRing.valuation R K
attribute [-simp] Subring.coe_subtype
open Matrix
variable {k l : ℕ+}
noncomputable section
def multFactor (g : Matrix (Fin k ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (j : Fin l) : R :=
  letI := Classical.typeDecidableEq K
  let x : K := g (Sum.inr ()) (Sum.inl j)
  have hvxvg : v x ≤ v (g (Sum.inr ()) (Sum.inr ())) := by
    rw [h]
    apply Matrix.coeff_le_coeffs_sup
  have hmem (hn : g (Sum.inr ()) (Sum.inr ()) ≠ 0) :
      -x * (g (Sum.inr ()) (Sum.inr ()))⁻¹ ∈ R := by
    simp only [mem_subring_iff_integer, neg_mul, Valuation.map_neg, _root_.map_mul, map_inv₀]
    have hnz : v (g (Sum.inr ()) (Sum.inr ())) ≠ 0 := (Valuation.ne_zero_iff v).mpr hn
    trans
    · exact mul_le_mul_of_nonneg_right hvxvg (le_of_lt (zero_lt_iff.mpr <| inv_ne_zero hnz))
    · rwa [GroupWithZero.mul_inv_cancel]
  if hn : g (Sum.inr ()) (Sum.inr ()) = 0 then 0
  else ⟨- x * (g (Sum.inr ()) (Sum.inr ()))⁻¹, hmem hn⟩
def rowEliminationTransvection (g : Matrix (Fin k ⊕ Unit) (Fin l ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (j : Fin l) :
    TransvectionStruct (Fin l ⊕ Unit) R :=
  ⟨Sum.inr (), Sum.inl j, Sum.inr_ne_inl, multFactor g h j⟩
lemma rowEliminationTransvection_mul_coeffs_sup' (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (j : Fin k) (c : R) :
    v ((g * transvection (Sum.inr ()) (Sum.inl j) (c : K)) (Sum.inr ()) (Sum.inr ())) =
      (g * transvection (Sum.inr ()) (Sum.inl j) (c : K)).coeffs_sup v := by
  apply le_antisymm
  · apply Matrix.coeff_le_coeffs_sup
  · apply Matrix.coeffs_sup_le
    intro a b
    by_cases he : b = Sum.inl j
    · subst he
      simp only [mul_transvection_apply_same, ne_eq, reduceCtorEq, not_false_eq_true,
        mul_transvection_apply_of_ne]
      trans
      · apply Valuation.map_add
      · simp only [_root_.map_mul, max_le_iff]
        constructor
        · rw [h]
          apply Matrix.coeff_le_coeffs_sup
        · have : (ValuationRing.valuation R K) c ≤ 1 := by
            rw [← mem_subring_iff_integer]
            simp only [SetLike.coe_mem]
          trans
          apply mul_le_mul' this (by rfl)
          rw [one_mul, h]
          apply Matrix.coeff_le_coeffs_sup
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, mul_transvection_apply_of_ne]
      rw [mul_transvection_apply_of_ne _ _ _ _ he, h]
      apply Matrix.coeff_le_coeffs_sup
def rowEliminationList (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    List (Matrix.TransvectionStruct (Fin k ⊕ Unit) R) :=
  List.ofFn (fun j : Fin k ↦ rowEliminationTransvection g h j)
def rowEliminationListMatrix (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    List (Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :=
  List.ofFn (fun j : Fin k ↦ (rowEliminationTransvection g h j).toMatrix)
attribute [-simp] Fin.natCast_eq_last Fin.coe_eq_castSucc
lemma rowEliminationList_get (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (n : Fin k) :
    (rowEliminationListMatrix g h)[n]? =
      (some <| transvection (Sum.inr ()) (Sum.inl n) (multFactor g h n)) := by
  simp [rowEliminationListMatrix, List.ofFnNthVal, rowEliminationTransvection]
def rowEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) : GL (Fin k ⊕ Unit) R :=
  (List.map (fun t ↦ TransvectionStruct.toGL t) (rowEliminationList g h)).prod
def colEliminator (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    GL (Fin k ⊕ Unit) R :=
  have : v (g.transpose (Sum.inr ()) (Sum.inr ())) = g.transpose.coeffs_sup v := by
    simpa [coeffs_sup_transpose]
  GL.transpose <| rowEliminator g.transpose this
lemma mul_rowEliminationListMatrix_coeffs_sup_aux (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) (r : ℕ) (hrk : r ≤ k) :
    v ((g * ((rowEliminationListMatrix g h).take r).prod) (Sum.inr ()) (Sum.inr ()))
      = (g * ((rowEliminationListMatrix g h).take r).prod).coeffs_sup v := by
  induction' r with n ih
  · simpa
  · let n' : Fin k := ⟨n, hrk⟩
    erw [List.take_succ, List.prod_append, rowEliminationList_get g h n']
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, map_transvection,
      Option.toList_some, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc]
    apply rowEliminationTransvection_mul_coeffs_sup'
    apply ih
    omega
lemma mul_rowEliminationListMatrix_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    v ((g * (rowEliminationListMatrix g h).prod) (Sum.inr ()) (Sum.inr ()))
      = (g * (rowEliminationListMatrix g h).prod).coeffs_sup v := by
  have hl : (rowEliminationListMatrix g h).length = k := by simp [rowEliminationListMatrix]
  rw [← List.take_length (l := rowEliminationListMatrix g h), hl]
  rw [mul_rowEliminationListMatrix_coeffs_sup_aux g h k le_rfl]
lemma mul_rowEliminator_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    v ((g * (rowEliminator g h).val) (Sum.inr ()) (Sum.inr ()))
      = (g * (rowEliminator g h).val).coeffs_sup v := by
  dsimp only [rowEliminator]
  rw [← map_listProd_toGL]
  simp only [rowEliminationList, List.map_ofFn]
  apply mul_rowEliminationListMatrix_coeffs_sup
lemma colEliminator_mul_coeffs_sup (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (h : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v) :
    v (((colEliminator g h).val * g) (Sum.inr ()) (Sum.inr ()))
      = ((colEliminator g h).val * g).coeffs_sup v := by
  simp only [colEliminator, GL.val_transpose]
  rw [← transpose_apply
    (((rowEliminator g.transpose _).val).transpose.map ⇑R.subtype * g) (Sum.inr ()) (Sum.inr ())]
  rw [transpose_mul]
  rw [← coeffs_sup_transpose]
  rw [transpose_mul]
  rw [transpose_map, transpose_transpose]
  apply mul_rowEliminator_coeffs_sup
structure IsNormalBlock (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) : Prop where
  isTwoBlockDiagonal : IsTwoBlockDiagonal g
  monotone : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v
set_option maxHeartbeats 300000
structure IsMonotoneDiag {n : Type*} [Fintype n] [Preorder n] (g : Matrix n n K) : Prop where
  isDiag : IsDiag g
  monotone : Monotone (fun j ↦ v (g j j))
structure IsBlockMonotoneDiag (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) : Prop where
  isDiag : IsDiag g
  monotone : Monotone (fun (j : Fin k) ↦ v (g (Sum.inl j) (Sum.inl j)))
  max_bot_right : v (g (Sum.inr ()) (Sum.inr ())) = g.coeffs_sup v
variable (ϖ : R) (hϖ : Irreducible ϖ)
def IsNormalDiag (g : Matrix (Fin k) (Fin k) K) : Prop :=
  ∃ (r : ℕ) (_ : r ≤ k) (f : Fin r → ℤ),
    Monotone f ∧ ∀ (j : Fin r), g j j = ϖ ^ f j ∧ ∀ (j : Fin k) (_ : r ≤ j), g j j = 0
@[simps!]
def cartanDiag {k : ℕ} (f : Fin k → ℤ) : GL (Fin k) K :=
  let d (j : Fin k) : Kˣ := {
    val := ϖ ^ f j
    inv := ϖ ^ (-f j)
    val_inv := by
      have : (↑ϖ ^ f j : K) ≠ 0 := by
        apply zpow_ne_zero
        intro hzero
        rw [Subring.coe_eq_zero_iff] at hzero
        apply Irreducible.ne_zero hϖ hzero
      simp [_root_.zpow_neg, this]
    inv_val := by
      have : (↑ϖ ^ f j : K) ≠ 0 := by
        apply zpow_ne_zero
        intro hzero
        rw [Subring.coe_eq_zero_iff] at hzero
        apply Irreducible.ne_zero hϖ hzero
      simp [_root_.zpow_neg, this]
  }
  GL.diagonal d


