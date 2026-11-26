-- Prove2me | solution 1 for ReweightedNPMLE.secondOrderCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:18.890042+00:00
-- url     : https://prove2.me/submissions/eee0d0aa-1778-420b-b3df-a4c9fb7c8e2c

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
open ReweightedNPMLE in
/-- If two second-order expansions are eventually ordered on the positive
side, then their quadratic coefficients have the same order. -/
theorem solution
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : f =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hg : g =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hle : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      f t + t ^ 2 * a ≤ g t + t ^ 2 * b) :
    a ≤ b := by
  have hfa : Tendsto (fun t : ℝ ↦ f t / t ^ 2 + a)
      (nhdsWithin 0 (Ioi 0)) (nhds a) := by
    simpa using hf.tendsto_div_nhds_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ a)
        (nhdsWithin 0 (Ioi 0)) (nhds a))
  have hgb : Tendsto (fun t : ℝ ↦ g t / t ^ 2 + b)
      (nhdsWithin 0 (Ioi 0)) (nhds b) := by
    simpa using hg.tendsto_div_nhds_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ b)
        (nhdsWithin 0 (Ioi 0)) (nhds b))
  apply le_of_tendsto_of_tendsto hfa hgb
  filter_upwards [hle, self_mem_nhdsWithin] with t ht htp
  have ht0 : t ≠ 0 := ne_of_gt htp
  have hspos : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  calc
    f t / t ^ 2 + a = (f t + t ^ 2 * a) / t ^ 2 := by
      field_simp [ht0]
    _ ≤ (g t + t ^ 2 * b) / t ^ 2 :=
      (div_le_div_iff_of_pos_right hspos).2 ht
    _ = g t / t ^ 2 + b := by
      field_simp [ht0]
