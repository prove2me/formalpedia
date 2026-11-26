-- Prove2me | Theorems.Thm_ReweightedNPMLE_secondOrderCoefficient_le
-- name    : ReweightedNPMLE.secondOrderCoefficient_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:46.235874+00:00
-- url     : https://prove2.me/theorems/20f0a923-b3db-575a-a14d-692ab457fc92
-- title:
--   Eventual ordering preserves quadratic expansion coefficients
-- statement:
--   Let $f,g:\mathbb R\to\mathbb R$ satisfy $f(t)=o(t^2)$ and $g(t)=o(t^2)$ as $t\downarrow0$. If for all sufficiently small positive $t$, $$f(t)+at^2\le g(t)+bt^2,$$ then $a\le b$. This isolates the quadratic coefficient comparison in the optimizer sensitivity argument.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L158-L187

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

theorem ReweightedNPMLE.secondOrderCoefficient_le
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : f =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hg : g =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hle : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      f t + t ^ 2 * a ≤ g t + t ^ 2 * b) :
    a ≤ b := by sorry
