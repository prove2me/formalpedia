-- Prove2me | solution 1 for ReweightedNPMLE.fittedLogDerivativeMatrix_isHermitian_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:01:25.098038+00:00
-- url     : https://prove2.me/submissions/df9f8431-92d5-4631-add0-fe4d30fbdbb2

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
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.FittedHessian.
section
/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE







@[simp] theorem fittedLogFunctionalMap_apply (n : ℕ)
    (z h : Fin n → ℝ) :
    fittedLogFunctionalMap n z h = ∑ i, h i * z i := by
  simp [fittedLogFunctionalMap, fittedLogLinearFunctional_apply]



@[simp] theorem fittedSecondDerivativeOfLogDerivative_apply {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (h k : Fin n → ℝ) :
    fittedSecondDerivativeOfLogDerivative J h k = ∑ i, k i * J h i := by
  simp [fittedSecondDerivativeOfLogDerivative]

theorem hasFDerivAt_fittedLogLinearFunctional {n : ℕ}
    {z : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ}
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    HasFDerivAt (fun u ↦ fittedLogLinearFunctional (z u))
      (fittedSecondDerivativeOfLogDerivative J) w := by
  have hcomp := (fittedLogFunctionalMap n).hasFDerivAt.comp w hz
  simpa [Function.comp_def, fittedSecondDerivativeOfLogDerivative] using hcomp







theorem fittedLogDerivative_symmetric_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w,
      HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h k : Fin n → ℝ) :
    ∑ i, k i * J h i = ∑ i, h i * J k i := by
  have hsecond := hasFDerivAt_fittedLogLinearFunctional hz
  simpa only [fittedSecondDerivativeOfLogDerivative_apply] using
    second_derivative_symmetric_of_eventually hpsi hsecond h k















end ReweightedNPMLE
end

/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w,
      HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    (fittedLogDerivativeMatrix J).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  let e : Fin n → Fin n → ℝ := fun j ↦ (Pi.single j 1 : Fin n → ℝ)
  simp only [star_trivial, fittedLogDerivativeMatrix, LinearMap.toMatrix'_apply]
  change J (e i) j = J (e j) i
  have hsingle (a : Fin n → ℝ) (r : Fin n) :
      ∑ l, e r l * a l = a r := by
    rw [Finset.sum_eq_single r]
    · simp [e]
    · intro l _ hl
      simp [e, hl]
    · simp
  have hs := fittedLogDerivative_symmetric_of_eventually psi z hpsi hz
    (e j) (e i)
  calc
    J (e i) j = ∑ l, e j l * J (e i) l := (hsingle (J (e i)) j).symm
    _ = ∑ l, e i l * J (e j) l := hs.symm
    _ = J (e j) i := hsingle (J (e j)) i
