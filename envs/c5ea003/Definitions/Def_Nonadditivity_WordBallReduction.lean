-- Prove2me | Definitions.Def_Nonadditivity_WordBallReduction
-- name    : Nonadditivity_WordBallReduction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:46:52.81798+00:00
-- url     : https://prove2.me/theorems/94b017e6-ffc7-4bda-8c4c-99354660128d
-- title:
--   Finite single-coordinate word balls in products of free groups
-- statement:
--   Reduced words in the free group on two generators are encoded by four signed letters and finite reduced tails, with inverse coding and length identities. Embedding a word into one coordinate of the product group preserves identity, inversion, and multiplication. A finite word ball contains the identity and these bounded-length single-coordinate embeddings. The radius used at reduction level $i$ is the integer ceiling of the original radius divided by $2^i$.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/WordBallReduction.lean#L20-L152

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
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





/-! Actual balls of reduced words in one tensor factor and their Gram reductions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.WordBallReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open PolynomialReduction
open Linearization

abbrev F₂ := FreeGroup (Fin 2)
abbrev G (n : ℕ) := Fin n → F₂

def letter (a : Letter) : Fin 2 × Bool := ![(0,true),(1,true),(1,false),(0,false)] a

def code (a : Fin 2 × Bool) : Letter :=
  if a.1=0 then (if a.2 then 0 else 3) else (if a.2 then 1 else 2)

@[simp] theorem letter_code (a : Fin 2 × Bool) : letter (code a) = a := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> decide

@[simp] theorem code_letter (a : Letter) : code (letter a) = a := by fin_cases a <;> decide



def tailLetters (a : Letter) : (t : ℕ) → ReducedTail a t → List (Fin 2 × Bool)
  | 0, _ => []
  | t+1, ⟨b,w⟩ => letter b.val :: tailLetters b.val t w

theorem length_tailLetters (a : Letter) (t : ℕ) (w : ReducedTail a t) :
    (tailLetters a t w).length = t := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => rcases w with ⟨b,w⟩; simp [tailLetters, ih]

def wordLetters {t : ℕ} (w : ReducedWord t) : List (Fin 2 × Bool) :=
  letter w.1 :: tailLetters w.1 t w.2

@[simp] theorem length_wordLetters {t : ℕ} (w : ReducedWord t) :
    (wordLetters w).length = t+1 := by simp [wordLetters, length_tailLetters]





abbrev WordIndex (r : ℕ) := Σ t : Fin r, ReducedWord t.val

def wordValue {r : ℕ} (w : WordIndex r) : F₂ := FreeGroup.mk (wordLetters w.2)



def single {n : ℕ} (j : Fin n) (v : F₂) : G n := fun k => if k=j then v else 1

@[simp] theorem single_one {n : ℕ} (j : Fin n) : single j 1 = 1 := by ext k; simp [single]
@[simp] theorem single_inv {n : ℕ} (j : Fin n) (v : F₂) : single j v⁻¹ = (single j v)⁻¹ := by
  ext k; by_cases h:k=j <;> simp [single,h]
@[simp] theorem single_mul {n : ℕ} (j : Fin n) (v w : F₂) :
    single j (v*w) = single j v * single j w := by
  ext k; by_cases h:k=j <;> simp [single,h]

def wordBall (n r : ℕ) : Finset (G n) :=
  insert 1 (Finset.univ.image (fun x : Fin n × WordIndex r => single x.1 (wordValue x.2)))

@[simp] theorem one_mem_wordBall (n r : ℕ) : (1:G n) ∈ wordBall n r := by simp [wordBall]











/-- The manuscript's ceiling of the word length divided by a power of two. -/
def radius (ell i : ℕ) : ℕ := ell ⌈/⌉ (2^i)

@[simp] theorem radius_zero (ell : ℕ) : radius ell 0 = ell := by simp [radius]















































end Nonadditivity.WordBallReduction


