-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedEnvelope
-- name    : ReweightedNPMLE_FittedEnvelope
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:23:12.145994+00:00
-- url     : https://prove2.me/theorems/6170807d-bc77-428b-8238-3e009111193f
-- title:
--   Likelihood value along a selector and its log-linear functional
-- statement:
--   For any selector \(\widehat v:\mathbb R^n\to\mathbb R^n\), define
--   \[
--   F_{\widehat v}(w)=\ell_w(\widehat v(w))
--   =\sum_iw_i\log\widehat v(w)_i.
--   \]
--   If the selector maximizes likelihood over a fixed feasible set, this is its optimized likelihood value. For \(z\in\mathbb R^n\), define the continuous linear functional
--   \[
--   \Lambda_z(h)=\sum_i h_i z_i.
--   \]
--   In the envelope argument, the relevant choice is \(z=\log\widehat v(w)\); continuity and optimality hypotheses establish that \(\Lambda_z\) is the Fréchet derivative of the optimized value. The definitions themselves do not impose these hypotheses.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedEnvelope.lean#L22-L33

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Envelope theorem for fitted likelihood values

The optimized weighted likelihood is a convex function of the weight vector.
The two optimizer inequalities squeeze its first-order remainder between zero
and a product involving the change in the fitted log-vector.  Consequently,
continuity of the fitted log-vector implies that it is the Fréchet derivative
of the optimal-value function.  Combining this envelope argument with the
local Lipschitz estimates from `FittedRegularity` gives the paper's gradient
identity on every locally bounded positive weight box.
-/

open Set Filter Asymptotics
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def fittedOptimalValue {n : ℕ}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) : ℝ :=
  weightedLogLikelihood w (vhat w)

noncomputable def fittedLogLinearFunctional {n : ℕ} (z : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, z i • ContinuousLinearMap.proj i

@[simp] theorem fittedLogLinearFunctional_apply {n : ℕ}
    (z h : Fin n → ℝ) :
    fittedLogLinearFunctional z h = ∑ i, h i * z i := by
  simp [fittedLogLinearFunctional, mul_comm]





















end ReweightedNPMLE


