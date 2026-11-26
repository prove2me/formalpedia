-- Prove2me | solution 1 for ReweightedNPMLE.eventually_mem_finiteSimplex_add_smul_zeroSum
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:59:30.098933+00:00
-- url     : https://prove2.me/submissions/b96c437d-788f-4958-b160-bdf43dfb220b

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
/-- A zero-total perturbation of a strictly positive probability vector stays
in the simplex for all sufficiently small scalar parameters. -/
theorem solution
    {k : ℕ} (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k)
    (hpfull : ∀ j, 0 < p j) (c : zeroSumCoefficients k) :
    ∀ᶠ t : ℝ in nhds 0, p + t • c.1 ∈ finiteSimplex k := by
  have hpos : ∀ᶠ t : ℝ in nhds 0, ∀ j, 0 < p j + t * c.1 j := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun t : ℝ ↦ p j + t * c.1 j) 0 := by fun_prop
    have hzero : 0 < p j + (0 : ℝ) * c.1 j := by simpa using hpfull j
    have ht := hc.tendsto (Ioi_mem_nhds hzero)
    simpa using ht
  filter_upwards [hpos] with t ht
  constructor
  · intro j
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (ht j).le
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib]
    rw [hp.2]
    have hc : ∑ j, c.1 j = 0 := c.property
    rw [← Finset.mul_sum, hc]
    simp
