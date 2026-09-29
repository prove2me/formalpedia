-- Prove2me | Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
-- name    : Zeta23.WeilEF.differentiableAt_GammaR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:39:18.517677+00:00
-- url     : https://prove2.me/theorems/0404866c-3347-4897-b816-6f541b02056a
-- title:
--   $\Gamma_{\mathbb{R}}$ is complex-differentiable on the right half-plane
-- statement:
--   Let $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\,\Gamma(s/2)$ denote the Archimedean Gamma factor (Mathlib's `Complex.GammaR`).
--
--   For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$,
--   $$\Gamma_{\mathbb{R}} \text{ is complex-differentiable at } s.$$
--   The factor $\pi^{-s/2}$ is entire, and $\Gamma(s/2)$ is holomorphic away from its poles at $s = 0, -2, -4, \dots$, all of which lie outside the open right half-plane.
--
--   This basic regularity fact is used throughout the contour arguments of the project: in the Weil explicit formula development (`EF_lit_zeta`, `completedZeta_zeros_strip`, `gamma_line_shift`, `horizontal_vanish`, `integrable_Fline`, `verticals_eq`) and in the Riemann-von Mangoldt zero-counting contour splits (`Zeta23.RvM.halfContour_completedZeta_split`, `horizontal_fold`, `vertical_fold`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/XiLogDeriv.lean#L29-L42

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Filter Topology

theorem Zeta23.WeilEF.differentiableAt_GammaR {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by sorry
