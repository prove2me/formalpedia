-- Prove2me | Theorems.Thm_Zeta23_norm_paperFT_le
-- name    : Zeta23.norm_paperFT_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:17.447098+00:00
-- url     : https://prove2.me/theorems/22ffa614-8749-45a0-84b0-67cbf71f1bfa
-- title:
--   Zeroth-order bound for $h_f$: $\|h_f(z)\| \le e^{|\mathrm{Im}\, z|\,\Lambda}\, \|f\|_1$
-- statement:
--   Here `paperFT` is the paper's Fourier convention $h_f(z) = \int_{\mathbb{R}} f(u)\, e^{izu}\, du$ (sign $+i$, no $2\pi$, complex argument $z$). Let $f : \mathbb{R} \to \mathbb{C}$ be integrable and supported in $[-\Lambda, \Lambda]$ — formalized as: $f(u) \ne 0$ implies $|u| \le \Lambda$. Then for every complex $z$,
--   $$\|h_f(z)\| \;\le\; e^{|\operatorname{Im} z| \cdot \Lambda} \int_{\mathbb{R}} \|f(u)\|\, du.$$
--   This is the zeroth-order case of the paper's decay bound [eq:hfbound]: on a horizontal strip the transform of a compactly supported function grows at most exponentially in the strip height, with rate given by the support radius.
--
--   The bound is the basic workhorse for controlling $h_f$ off the real axis — needed because the explicit formula is evaluated at the ordinates $\gamma_\rho$ of possibly off-line zeros, which have $|\operatorname{Im} \gamma_\rho| < 1/2$. From the module `Zeta23.Poisson.PaperFT` it feeds the explicit-formula estimates (`Zeta23.EF.integrable_paperFT_mul_mu`, `norm_fourier_mul_one_add_sq_le`), the taper bounds (`Zeta23.Taper.abs_PhiR_le_L`, `norm_phiHat_le`, and others), the Weil explicit-formula development (`Zeta23.WeilEF.norm_Hfn_le`, `norm_paperFT_le_uniform`), and the second-order bound `Zeta23.norm_paperFT_mul_sq_le`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson/PaperFT.lean#L79-L90, docstring tag [eq:hfbound]

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

theorem Zeta23.norm_paperFT_le {f : ℝ → ℂ} {Λ : ℝ} (hfi : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖f u‖ := by sorry
