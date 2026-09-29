-- Prove2me | Theorems.Thm_Zeta23_Taper_norm_paperFT_mul_le
-- name    : Zeta23.Taper.norm_paperFT_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:04.551719+00:00
-- url     : https://prove2.me/theorems/da7babef-822d-4b72-939f-3b1f903a6770
-- title:
--   First-order transform decay [eq:hfbound]: $\|h_f(z)\|\,\|z\| \le e^{|\mathrm{Im}\,z|\Lambda}\,\|f'\|_1$
-- statement:
--   For $f : \mathbb{R} \to \mathbb{C}$ let $h_f(z) := \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ denote the paper Fourier transform (`paperFT`), defined for every complex argument $z$.
--
--   Suppose $f$ is continuously differentiable ($C^1$) and its support is contained in $[-\Lambda, \Lambda]$ (formally: $f(u) \ne 0$ implies $|u| \le \Lambda$). Then for every $z \in \mathbb{C}$,
--   $$\|h_f(z)\| \cdot \|z\| \;\le\; e^{|\operatorname{Im} z|\,\Lambda} \int_{\mathbb{R}} \|f'(u)\|\,du.$$
--   This is the first-order case of the transform bound [eq:hfbound], obtained by a single integration by parts; it is the companion of the second-order bound `Zeta23.norm_paperFT_mul_sq_le` (two integrations by parts, decay $\|z\|^{-2}$).
--
--   In the project it supplies the $|r|^{-1}$-decay estimates for the taper transforms: it is consumed by `Zeta23.Taper.abs_phiHatR_mul_abs_le` and `Zeta23.Taper.abs_PhiR_mul_abs_le`, which together with the trivial and second-order bounds establish the majorant $\psi$ of [eq:psidef].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L239-L255, docstring tag [eq:hfbound]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.norm_paperFT_mul_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv f u‖ := by sorry
