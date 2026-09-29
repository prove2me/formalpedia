-- Prove2me | Theorems.Thm_Zeta23_paperFT_deriv
-- name    : Zeta23.paperFT_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:22.853806+00:00
-- url     : https://prove2.me/theorems/8d056631-09b8-42b0-bc1c-bb1021753259
-- title:
--   Integration by parts: $h_{f'}(z) = -iz\, h_f(z)$
-- statement:
--   With $h_f(z) = \int_{\mathbb{R}} f(u)\, e^{izu}\, du$ the paper's Fourier transform (`paperFT`), let $f : \mathbb{R} \to \mathbb{C}$ be continuously differentiable ($C^1$) with compact support. Then for every complex $z$, one integration by parts gives
--   $$h_{f'}(z) \;=\; -\,(i z)\, h_f(z),$$
--   where $f' = $ `deriv` $f$; the boundary terms vanish by compact support.
--
--   This is the standard derivative-to-multiplier rule in the paper's convention (sign $+i$, no $2\pi$), and it is the engine behind the decay bounds [eq:hfbound]: applying it twice converts $\|z\|^2\, \|h_f(z)\|$ into $\|h_{f''}(z)\|$. From `Zeta23.Poisson.PaperFT` it is consumed by `Zeta23.norm_paperFT_mul_sq_le` (the second-order bound) and by `Zeta23.Taper.norm_paperFT_mul_le` (the first-order taper bound).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson/PaperFT.lean#L92-L116

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

theorem Zeta23.paperFT_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (z : ℂ) :
    paperFT (deriv f) z = -(I * z) * paperFT f z := by sorry
