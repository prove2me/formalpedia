-- Prove2me | Definitions.Def_Nonadditivity_ObservableDimension
-- name    : Nonadditivity_ObservableDimension
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:36:26.453647+00:00
-- url     : https://prove2.me/theorems/f7075084-678f-4e54-95cf-c3e683d0227b
-- title:
--   The real vector space and trace of Hermitian observables
-- statement:
--   Let $I$ be a finite matrix index set with decidable equality. Hermitian complex matrices form the real vector space
--   $$\mathcal H_I=\{A\in M_I(\mathbb C):A^*=A\}.$$
--   The bundle supplies its finite-dimensionality instance over $\mathbb R$ and the real linear trace functional
--   $$\tau:\mathcal H_I\to\mathbb R,\qquad \tau(A)=\operatorname{Re}\operatorname{Tr}A.$$
--   The evaluation identity for $\tau$ is proved explicitly. These structures support finite-dimensional compactness, trace constraints, and observable-net arguments using the standard real scalar structure on self-adjoint matrices.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ObservableDimension.lean#L41-L54

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Nonadditivity.QuantitativeNet
end Nonadditivity.QuantitativeNet

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/







/-! # Exact real dimension of traceless Hermitian observables

The imaginary-part map and real trace give two rank-nullity identities.
No explicit choice of a Hermitian basis is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.ObservableDimension

open scoped BigOperators
open FiniteRealization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



instance selfAdjoint_matrix_finiteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  FiniteDimensional.of_surjective (imaginaryPart (A := Matrix ι ι ℂ))
    imaginaryPart_surjective

/-- Real trace restricted to actual self-adjoint matrices. -/
def hermitianTrace : selfAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (A : Matrix ι ι ℂ)).re
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' r A := by simp [Matrix.trace_smul]

omit [DecidableEq ι] in
@[simp] theorem hermitianTrace_apply (A : selfAdjoint (Matrix ι ι ℂ)) :
    hermitianTrace A = (Matrix.trace (A : Matrix ι ι ℂ)).re := rfl













end Nonadditivity.ObservableDimension


