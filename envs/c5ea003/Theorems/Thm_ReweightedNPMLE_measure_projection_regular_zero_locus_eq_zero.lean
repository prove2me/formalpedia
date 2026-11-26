-- Prove2me | Theorems.Thm_ReweightedNPMLE_measure_projection_regular_zero_locus_eq_zero
-- name    : ReweightedNPMLE.measure_projection_regular_zero_locus_eq_zero
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:59.128166+00:00
-- url     : https://prove2.me/theorems/5893f706-3b2b-5dfb-82b7-37a9968138e7
-- title:
--   Null projection of an entire regular zero locus
-- statement:
--   Let $X,H,D$ be finite-dimensional real normed spaces, $\mu$ additive Haar measure on the Borel space $D$, and $\pi:X\to D$ continuous linear. Let $g:X\to H$ be continuously differentiable. If $\dim X<\dim D+\dim H$, then $$\mu\bigl(\pi\{x:g(x)=0,\ Dg(x)\text{ surjective}\}\bigr)=0.$$ This globalizes the local implicit-function projection estimate.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/IncidenceProjection.lean#L63-L89

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Null projections of regular level sets

The implicit function theorem parameterizes a regular level set locally by
the kernel of its derivative. Strict differentiability of this chart gives
a Lipschitz neighborhood, whose lower-dimensional image is Haar-null.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

theorem ReweightedNPMLE.measure_projection_regular_zero_locus_eq_zero
    {X H D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D]
    (μ : Measure D) [IsAddHaarMeasure μ] (π : X →L[ℝ] D)
    (g : X → H) (hg : ContDiff ℝ 1 g)
    (hdim : Module.finrank ℝ X < Module.finrank ℝ D + Module.finrank ℝ H) :
    μ (π '' {x | g x = 0 ∧ Function.Surjective (fderiv ℝ g x)}) = 0 := by sorry
