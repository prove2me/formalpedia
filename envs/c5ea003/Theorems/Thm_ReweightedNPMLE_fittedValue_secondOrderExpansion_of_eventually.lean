-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedValue_secondOrderExpansion_of_eventually
-- name    : ReweightedNPMLE.fittedValue_secondOrderExpansion_of_eventually
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:59.46682+00:00
-- url     : https://prove2.me/theorems/571b7671-b393-4b39-8708-07b41ab4383c
-- title:
--   Local second-order expansion from an envelope gradient identity
-- statement:
--   Let $\psi:\mathbb R^n\to\mathbb R$ and $z:\mathbb R^n\to\mathbb R^n$. Suppose that throughout some neighborhood of $w$, $\psi$ is Fréchet differentiable and
--   $$
--   D\psi(q)[h]=\sum_i h_i z(q)_i.
--   $$
--   Assume $z$ is Fréchet differentiable at $w$, with derivative $J$. Then for every fixed direction $h\in\mathbb R^n$,
--   $$
--   \psi(w+th)=\psi(w)+t\sum_i h_i z(w)_i
--   +\frac{t^2}{2}\sum_i h_i(Jh)_i+o(t^2)
--   \quad(t\downarrow0).
--   $$
--   Only a local gradient identity and differentiability of $z$ at the base point are required.
--
--   This turns the first-order envelope relation into the directional quadratic expansion needed for likelihood curvature and support sensitivity.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L172-L262

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

theorem ReweightedNPMLE.fittedValue_secondOrderExpansion_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt psi (fittedLogLinearFunctional (z q)) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h : Fin n → ℝ) :
    (fun t : ℝ ↦ psi (w + t • h) - psi w -
        t * (∑ i, h i * z w i) -
        (t ^ 2 / 2) * (∑ i, h i * J h i)) =o[nhdsWithin 0 (Ioi 0)]
      (fun t : ℝ ↦ t ^ 2) := by sorry
