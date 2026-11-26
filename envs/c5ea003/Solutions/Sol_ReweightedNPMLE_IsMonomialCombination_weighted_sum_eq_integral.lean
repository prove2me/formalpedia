-- Prove2me | solution 1 for ReweightedNPMLE.IsMonomialCombination.weighted_sum_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:33.255454+00:00
-- url     : https://prove2.me/submissions/de6495b8-c297-478f-acda-379b5448db95

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
/-- A finite law and an integrable law with the same feature barycenter have
the same average for every polynomial represented by those features. -/
theorem solution
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d D (z i) =
      ∫ a, monomialFeature d D (θ a) ∂μ) :
    ∑ i, w i * f (z i) = ∫ a, f (θ a) ∂μ := by
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
  calc
    (∑ i, w i * f (z i)) = L (∑ i, w i • monomialFeature d D (z i)) := by
      rw [map_sum]
      apply Fintype.sum_congr
      intro i
      rw [map_smul, hL]
      rfl
    _ = L (∫ a, monomialFeature d D (θ a) ∂μ) := congrArg L hmom
    _ = ∫ a, L (monomialFeature d D (θ a)) ∂μ :=
      (L.integral_comp_comm hint).symm
    _ = ∫ a, f (θ a) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ hL (θ a)
