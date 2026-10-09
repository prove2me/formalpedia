-- Prove2me | Definitions.Def_Nonadditivity_FiniteFreeModel
-- name    : Nonadditivity_FiniteFreeModel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:44:51.238975+00:00
-- url     : https://prove2.me/theorems/09197243-8e63-41af-bc7e-ca2e9740eb88
-- title:
--   Finite permutation models that detect bounded free words
-- statement:
--   Let $F(\alpha)$ be the free group on a finite alphabet $\alpha$, with reduced-word length $|w|$, and fix an integer radius $R\ge0$. Its word ball $B_R=\{w:|w|\le R\}$ is finite. Partial left translation by each generator is completed to a permutation of $B_R$, producing a homomorphism
--   $$\pi_R:F(\alpha)\longrightarrow\operatorname{Perm}(B_R).$$
--   With the identity word as distinguished base point, every $|w|\le R$ satisfies $\pi_R(w)(1)=w$. Consequently,
--   $$|w|\le R\ \Longrightarrow\ \bigl(\pi_R(w)=1\ \Longleftrightarrow\ w=1\bigr).$$
--   The bundle constructs the finite ball, its injective encoding by bounded lists of oriented letters, the completed permutations, and these exact bounded-word identities. This supplies finite group models with exact separation at a chosen radius.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteFreeModel.lean#L19-L116

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! Finite quotients that exactly distinguish every word in a prescribed free-group ball. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.FiniteFreeModel
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

abbrev Ball (α : Type*) [DecidableEq α] (R : ℕ) := {w : FreeGroup α // FreeGroup.norm w ≤ R}

def encode (R : ℕ) (w : Ball α R) : Σ t : Fin (R+1), List.Vector (α×Bool) t.val :=
  ⟨⟨w.val.toWord.length,by have := w.property; change w.val.toWord.length ≤ R at this; omega⟩,
    ⟨w.val.toWord,rfl⟩⟩

theorem encode_injective (R : ℕ) : Function.Injective (encode (α := α) R) := by
  intro v w h
  have hwords := congrArg (fun x : Σ t : Fin (R+1), List.Vector (α×Bool) t.val => x.2.val) h
  exact Subtype.ext (FreeGroup.toWord_injective hwords)

instance ballFintype (R : ℕ) : Fintype (Ball α R) := Fintype.ofInjective (encode R) (encode_injective R)

def base (R : ℕ) : Ball α R := ⟨1,by simp⟩

/-- Left translation restricted to pairs that remain inside the finite ball. -/
def partialTranslation (R : ℕ) (a : α) :
    {w : Ball α R // FreeGroup.norm (FreeGroup.of a * w.val) ≤ R} ≃
    {w : Ball α R // FreeGroup.norm ((FreeGroup.of a)⁻¹ * w.val) ≤ R} where
  toFun w := ⟨⟨FreeGroup.of a * w.val.val,w.property⟩,by simpa only [inv_mul_cancel_left] using w.val.property⟩
  invFun w := ⟨⟨(FreeGroup.of a)⁻¹ * w.val.val,w.property⟩,by simpa only [mul_inv_cancel_left] using w.val.property⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; apply Subtype.ext; simp

/-- Complete the partial translation to a genuine finite permutation. -/
def generatorPerm (R : ℕ) (a : α) : Equiv.Perm (Ball α R) := (partialTranslation R a).extendSubtype

theorem generatorPerm_apply (R : ℕ) (a : α) (w : Ball α R)
    (h : FreeGroup.norm (FreeGroup.of a * w.val) ≤ R) :
    (generatorPerm R a w).val = FreeGroup.of a * w.val := by
  rw [generatorPerm,Equiv.extendSubtype_apply_of_mem _ w h]
  rfl

theorem generatorPerm_inv_apply (R : ℕ) (a : α) (w : Ball α R)
    (h : FreeGroup.norm ((FreeGroup.of a)⁻¹ * w.val) ≤ R) :
    ((generatorPerm R a)⁻¹ w).val = (FreeGroup.of a)⁻¹ * w.val := by
  let v : Ball α R := ⟨(FreeGroup.of a)⁻¹*w.val,h⟩
  have hv : generatorPerm R a v = w := by
    apply Subtype.ext
    rw [generatorPerm_apply]
    · simp [v]
    · simpa [v] using w.property
  have heq : (generatorPerm R a)⁻¹ w = v := by
    rw [←hv]
    exact (generatorPerm R a).symm_apply_apply v
  exact congrArg Subtype.val heq

/-- A homomorphism into a genuine finite group, with no approximation premise. -/
def model (R : ℕ) : FreeGroup α →* Equiv.Perm (Ball α R) := FreeGroup.lift (generatorPerm R)

theorem mk_cons_true (a : α) (l : List (α×Bool)) :
    FreeGroup.mk ((a,true)::l) = FreeGroup.of a * FreeGroup.mk l := by
  rw [FreeGroup.of,FreeGroup.mul_mk]
  rfl

theorem mk_cons_false (a : α) (l : List (α×Bool)) :
    FreeGroup.mk ((a,false)::l) = (FreeGroup.of a)⁻¹ * FreeGroup.mk l := by
  rw [FreeGroup.of,FreeGroup.inv_mk,FreeGroup.mul_mk]
  rfl

/-- Every word of length at most `R` acts correctly on the distinguished identity. -/
theorem model_mk_base (R : ℕ) (l : List (α×Bool)) (hl : l.length ≤ R) :
    ((model R (FreeGroup.mk l)) (base R)).val = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hl' : l.length ≤ R := by simp only [List.length_cons] at hl; omega
    specialize ih hl'
    rcases x with ⟨a,b⟩
    cases b with
    | false =>
      rw [mk_cons_false,map_mul,map_inv]
      change ((generatorPerm R a)⁻¹ ((model R (FreeGroup.mk l)) (base R))).val = _
      rw [generatorPerm_inv_apply]
      · rw [ih]
      · rw [ih,←mk_cons_false]
        exact FreeGroup.norm_mk_le.trans hl
    | true =>
      rw [mk_cons_true,map_mul]
      change (generatorPerm R a ((model R (FreeGroup.mk l)) (base R))).val = _
      rw [generatorPerm_apply]
      · rw [ih]
      · rw [ih,←mk_cons_true]
        exact FreeGroup.norm_mk_le.trans hl

theorem model_base (R : ℕ) (w : FreeGroup α) (hw : FreeGroup.norm w ≤ R) :
    ((model R w) (base R)).val = w := by
  simpa only [FreeGroup.mk_toWord] using model_mk_base R w.toWord hw

/-- The constructed finite model detects every nontrivial element in the chosen ball. -/
theorem model_eq_one_iff (R : ℕ) (w : FreeGroup α) (hw : FreeGroup.norm w ≤ R) :
    model R w = 1 ↔ w = 1 := by
  constructor
  · intro h
    have hb := model_base R w hw
    rw [h] at hb
    exact hb.symm
  · rintro rfl; exact map_one _









end Nonadditivity.FiniteFreeModel


