-- Prove2me | Definitions.Def_Nonadditivity_PolynomialDilation
-- name    : Nonadditivity_PolynomialDilation
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:46:22.529658+00:00
-- url     : https://prove2.me/theorems/285fc0cc-8a8e-47c7-8bf8-f989daaf1cd7
-- title:
--   Symmetric support and doubled polynomial coefficients
-- statement:
--   The symmetric support of a finite group-word polynomial is its support together with all inverse words. The dilation uses a direct sum of two copies of the coefficient index type and inverse-transpose block coefficients on this symmetric support. Its coefficient dimension is exactly twice the original dimension. This construction provides the algebraic data for the Hermitian dilation used in the polynomial reduction pipeline.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/PolynomialDilation.lean#L18-L38

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



/-! # Final self-adjoint linear polynomial with unchanged comparison error -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.PolynomialReduction.Polynomial
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open FiniteSetFactorization
variable {G : Type} [Group G] [DecidableEq G]

def symmetricSupport (P : Polynomial G) : Finset G :=
  P.support ∪ P.support.image (fun w => w⁻¹)



def dilate (P : Polynomial G) : Polynomial G where
  Index := P.Index ⊕ P.Index
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := P.symmetricSupport
  coefficient := dilationCoefficient P.normalizedCoefficient

@[simp] theorem dilate_dimension (P : Polynomial G) :
    Fintype.card P.dilate.Index = 2*Fintype.card P.Index := by
  simp [dilate, two_mul]













end Nonadditivity.PolynomialReduction.Polynomial

namespace Nonadditivity.ProductPolynomialReduction
open PolynomialReduction
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type} [DecidableEq α] {n : ℕ}





end Nonadditivity.ProductPolynomialReduction


