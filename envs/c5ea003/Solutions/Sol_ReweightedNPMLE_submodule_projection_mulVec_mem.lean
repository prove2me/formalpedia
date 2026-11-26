-- Prove2me | solution 1 for ReweightedNPMLE.submodule_projection_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:01:03.846289+00:00
-- url     : https://prove2.me/submissions/72aa59df-5881-4f9f-8799-fb90d6504951

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.SupportSensitivity.
section
/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

namespace ReweightedNPMLE

















































theorem submoduleOrthonormalMatrix_column_mem {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (j : Fin (Module.finrank ℝ S)) :
    matrixColumnEuclidean (submoduleOrthonormalMatrix S) j ∈ S := by
  change ((stdOrthonormalBasis ℝ S j : S) : EuclideanSpace ℝ (Fin n)) ∈ S
  exact (stdOrthonormalBasis ℝ S j).property















end ReweightedNPMLE
end

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Multiplying by the orthogonal-projection matrix associated with the
canonical orthonormal basis of a submodule produces a vector in that
submodule. -/
theorem solution {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    WithLp.toLp 2 (((submoduleOrthonormalMatrix S) *
      (submoduleOrthonormalMatrix S)ᴴ) *ᵥ x) ∈ S := by
  let V := submoduleOrthonormalMatrix S
  let b : Fin (Module.finrank ℝ S) → ℝ := Vᴴ *ᵥ x
  have hsum : WithLp.toLp 2 (V *ᵥ b) =
      ∑ j, b j • matrixColumnEuclidean V j := by
    apply PiLp.ext
    intro i
    simp [Matrix.mulVec, dotProduct, matrixColumnEuclidean, mul_comm]
  change WithLp.toLp 2 ((V * Vᴴ) *ᵥ x) ∈ S
  rw [← Matrix.mulVec_mulVec]
  change WithLp.toLp 2 (V *ᵥ b) ∈ S
  rw [hsum]
  exact S.sum_mem fun j _ ↦ S.smul_mem (b j)
    (submoduleOrthonormalMatrix_column_mem S j)
