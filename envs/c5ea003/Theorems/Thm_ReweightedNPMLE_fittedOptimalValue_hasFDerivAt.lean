-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedOptimalValue_hasFDerivAt
-- name    : ReweightedNPMLE.fittedOptimalValue_hasFDerivAt
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:38.821191+00:00
-- url     : https://prove2.me/theorems/17a88335-1a75-45a2-a671-d91af7494a1b
-- title:
--   Envelope derivative of the optimized weighted likelihood
-- statement:
--   Let $C\subset\mathbb R^n$, and suppose $\widehat v(q)$ maximizes $\sum_iq_i\ell(v_i)$ over $C$ for every real weight vector $q$. Interpret $\ell(x)$ as $\log|x|$ for $x\ne0$ and as zero at $x=0$. Define $F(q)=\sum_iq_i\ell(\widehat v(q)_i)$ and $z(q)_i=\ell(\widehat v(q)_i)$. If $z$ is continuous at $w$, then $F$ is Fréchet differentiable there, with
--   $$
--   DF(w)[h]=\sum_{i=1}^n h_i z(w)_i
--   \qquad\text{for every }h\in\mathbb R^n.
--   $$
--   No differentiability of the optimizer selection is assumed.
--
--   For positive fitted vectors, this is the usual envelope identity identifying the fitted log-vector as the gradient of optimized likelihood.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedEnvelope.lean#L132-L191

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
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
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

open ReweightedNPMLE

theorem ReweightedNPMLE.fittedOptimalValue_hasFDerivAt {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ)
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (hzcont : ContinuousAt
      (fun u i ↦ Real.log (vhat u i)) w) :
    HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat w i))) w := by sorry
