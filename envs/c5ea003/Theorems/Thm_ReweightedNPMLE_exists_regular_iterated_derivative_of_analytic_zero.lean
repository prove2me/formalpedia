-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_regular_iterated_derivative_of_analytic_zero
-- name    : ReweightedNPMLE.exists_regular_iterated_derivative_of_analytic_zero
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:47.337621+00:00
-- url     : https://prove2.me/theorems/7fee1d5f-82bc-5c33-a309-1bcf5fc87952
-- title:
--   Detecting an analytic zero by a regular coordinate derivative
-- statement:
--   Let $E$ be a real normed vector space with a finite basis $(b_1,\ldots,b_d)$, and let $f:E\to\mathbb R$ be globally real analytic and not identically zero. If $f(x)=0$, there exist $m\ge0$, a basis index $\ell$, and a word $\sigma=(\sigma_1,\ldots,\sigma_m)$ of basis indices such that the scalar function
--   $$g(y)=D^m f(y)[b_{\sigma_1},\ldots,b_{\sigma_m}]$$
--   satisfies $g(x)=0$ and $Dg(x)[b_\ell]\ne0$. Thus every zero belongs to a regular zero set of some finite-order coordinate derivative, even when the original zero is singular.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/AnalyticIncidence.lean#L60-L96

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Analytic derivative detection for incidence sets

A nontrivial globally real-analytic scalar function has a nonzero derivative
of some finite order at every point. This supplies the minimal derivative
order used to turn possibly singular zero sets into regular level sets.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology ENNReal NNReal

theorem ReweightedNPMLE.exists_regular_iterated_derivative_of_analytic_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (b : Module.Basis (Fin d) ℝ E) (f : E → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hnonzero : ∃ y, f y ≠ 0) (x : E) (hx : f x = 0) :
    ∃ (m : ℕ) (ℓ : Fin d) (σ : Fin m → Fin d),
      iteratedFDeriv ℝ m f x (fun i ↦ b (σ i)) = 0 ∧
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m f y (fun i ↦ b (σ i))) x (b ℓ) ≠ 0 := by sorry
