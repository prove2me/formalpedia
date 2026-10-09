-- Prove2me | Definitions.Def_Nonadditivity_RegularShiftedDilation
-- name    : Nonadditivity_RegularShiftedDilation
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:39:13.203887+00:00
-- url     : https://prove2.me/theorems/16aa8b9f-afe9-431f-985e-26c9c9ebd0fd
-- title:
--   Nontriviality of the coefficient-valued regular Hilbert space
-- statement:
--   Let $G$ be a group and $I$ a finite nonempty coefficient index set. The coefficient-valued regular Hilbert space is
--   $$\mathcal H(G,I)=\ell^2(G;\mathbb C^I).$$
--   This bundle provides its nontriviality instance: it contains two distinct vectors, equivalently a nonzero vector. A vector supported at the identity of $G$ with a nonzero coefficient supplies the witness. The instance enables operator and spectral arguments that require a nontrivial Hilbert space.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularShiftedDilation.lean#L126-L133

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularRestriction
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
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




/-! # The exact shifted norm of an infinite regular dilation

The grading unitary makes the spectrum symmetric, so its positive endpoint
is the original polynomial norm. No finite-dimensional spectral assumption
is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularShiftedDilation

open RegularCoefficientEnergy RegularDilation
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

section Lift

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]



end Lift

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]











instance hilbertNontrivial [Nonempty ι] : Nontrivial (Hilbert G ι) := by
  classical
  let i : ι := Classical.choice inferInstance
  let x : CoefficientSpace ι := WithLp.toLp 2 (fun _ => (1 : ℂ))
  refine ⟨⟨lp.single 2 (1 : G) x, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun f : Hilbert G ι => f 1 i) h
  simp [x] at he





end Nonadditivity.RegularShiftedDilation


