-- Prove2me | Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le
-- name    : Zeta23.norm_paperFT_mul_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:28.316098+00:00
-- url     : https://prove2.me/theorems/96169fc4-eb00-4226-a399-77c953eaa2c6
-- title:
--   Second-order bound for $h_f$: $\|h_f(z)\| \cdot \|z\|^2 \le e^{|\mathrm{Im}\, z|\,\Lambda}\, \|f''\|_1$
-- statement:
--   With $h_f(z) = \int_{\mathbb{R}} f(u)\, e^{izu}\, du$ the paper's Fourier transform (`paperFT`), let $f : \mathbb{R} \to \mathbb{C}$ be twice continuously differentiable ($C^2$) and supported in $[-\Lambda, \Lambda]$ (i.e. $f(u) \ne 0 \Rightarrow |u| \le \Lambda$). Then for every complex $z$,
--   $$\|h_f(z)\| \cdot \|z\|^2 \;\le\; e^{|\operatorname{Im} z| \cdot \Lambda} \int_{\mathbb{R}} \|f''(u)\|\, du,$$
--   where $f''$ is the iterated `deriv`. This is the second-order case of [eq:hfbound]: two integrations by parts ($h_{f'}(z) = -iz\, h_f(z)$, proved as `paperFT_deriv`) convert quadratic decay in $\|z\|$ into the $L^1$ norm of $f''$, at the cost of the same exponential strip factor.
--
--   The resulting $\|z\|^{-2}$ decay is what makes the sums over zeros in the explicit formula absolutely convergent and the tail estimates summable. From `Zeta23.Poisson.PaperFT` it is consumed across the analytic core: the explicit-formula module (`Zeta23.EF.integrable_paperFT_mul_mu`, `norm_fourier_mul_one_add_sq_le`), the tail package (`Zeta23.Tail.eventually_tailPackage`), the taper estimates (`Zeta23.Taper.abs_PhiR_mul_sq_le`, `abs_phiHatR_mul_sq_le`, `hasSum_phiHatR_mul`, and others), and the Weil explicit-formula development (`Zeta23.WeilEF.EF_zero_sum_summable_gen`, `norm_Hfn_le`, `norm_paperFT_le_uniform`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson/PaperFT.lean#L137-L153, docstring tag [eq:hfbound]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23

theorem Zeta23.norm_paperFT_mul_sq_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ := by sorry
