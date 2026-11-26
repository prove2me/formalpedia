-- Prove2me | solution 1 for ReweightedNPMLE.IsMonomialCombination.integrable_comp_of_feature
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:31.60966+00:00
-- url     : https://prove2.me/submissions/e584fa3b-f3ef-4e49-a022-d0abce283b5e

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE.IsMonomialCombination in
/-- Integrability of the whole finite feature vector implies integrability of
each polynomial represented by that vector. -/
theorem solution
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    MeasureTheory.Integrable (fun a ↦ f (θ a)) μ := by
  classical
  obtain ⟨c, hc⟩ := hf
  let L : (MonomialCoord d D → ℝ) →L[ℝ] ℝ :=
    ∑ m, c m • ContinuousLinearMap.proj m
  have hL (u : Fin d → ℝ) : L (monomialFeature d D u) = f u := by
    rw [hc]
    dsimp only [L]
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, monomialFeature]
  exact (L.integrable_comp hint).congr
    (Filter.Eventually.of_forall fun a ↦ hL (θ a))
