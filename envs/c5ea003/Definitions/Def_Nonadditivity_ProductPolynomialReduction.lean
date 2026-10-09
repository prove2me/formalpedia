-- Prove2me | Definitions.Def_Nonadditivity_ProductPolynomialReduction
-- name    : Nonadditivity_ProductPolynomialReduction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:45:37.891518+00:00
-- url     : https://prove2.me/theorems/b08d87a8-d68d-46bf-acc3-9a4598f8d894
-- title:
--   Finite word data for products of free groups
-- statement:
--   A word in a finite product of free groups has total degree equal to the sum of its coordinate reduced-word lengths. The identity has degree zero, inversion preserves degree, and a single coordinate generator has degree one. Labeled generators define an evaluation homomorphism from one free group into the product, while ordered concatenation gives a canonical word presentation. Prefix and suffix cuts define a finite support containing the identity for the shortening construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ProductPolynomialReduction.lean#L24-L132

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
import Mathlib.Algebra.BigOperators.Fin
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




/-! # Actual word shortening on products of free groups

A canonical concatenation of coordinate words supplies a finite word
presentation. Prefix/suffix cuts therefore reduce the total product degree;
no commutation assumption between letters within a factor is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.ProductPolynomialReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction

variable {α : Type} [DecidableEq α] {n : ℕ}
abbrev GroupWord (α : Type) (n : ℕ) := Fin n → FreeGroup α

def degree (w : GroupWord α n) : ℕ := ∑ j, FreeGroup.norm (w j)

@[simp] theorem degree_one : degree (1 : GroupWord α n) = 0 := by simp [degree]
@[simp] theorem degree_inv (w : GroupWord α n) : degree w⁻¹ = degree w := by simp [degree]



def generator (x : Fin n × α) : GroupWord α n :=
  fun j => if j=x.1 then FreeGroup.of x.2 else 1

@[simp] theorem degree_generator (x : Fin n × α) : degree (generator x) = 1 := by
  simp [degree, generator, apply_ite FreeGroup.norm]

def evaluate : FreeGroup (Fin n × α) →* GroupWord α n := FreeGroup.lift generator



/-- A coordinate word mapped into the free group on all labeled generators. -/
def localWord (j : Fin n) (v : FreeGroup α) : FreeGroup (Fin n × α) :=
  FreeGroup.map (fun a => (j,a)) v





/-- Canonical ordered concatenation, preserving the sum of coordinate lengths. -/
def flatten (w : GroupWord α n) : FreeGroup (Fin n × α) :=
  ((List.finRange n).map (fun j => localWord j (w j))).prod





def firstPart (r : ℕ) (w : GroupWord α n) : GroupWord α n :=
  evaluate (firstHalf r (flatten w))
def secondPart (r : ℕ) (w : GroupWord α n) : GroupWord α n :=
  evaluate (suffix r (flatten w))







/-- Deterministic support obtained from the two halves of every canonical word. -/
def splitSupport (T : Finset (GroupWord α n)) (r : ℕ) : Finset (GroupWord α n) :=
  insert 1 ((T.image fun w => (firstPart r w)⁻¹) ∪ T.image (secondPart r))

@[simp] theorem one_mem_splitSupport (T : Finset (GroupWord α n)) (r : ℕ) :
    (1 : GroupWord α n) ∈ splitSupport T r := by simp [splitSupport]





































end Nonadditivity.ProductPolynomialReduction


