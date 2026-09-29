-- Prove2me | Theorems.Thm_Zeta23_Poisson_isBigO_of_decay
-- name    : Zeta23.Poisson.isBigO_of_decay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:58:31.550642+00:00
-- url     : https://prove2.me/theorems/1b35c2f0-d2e3-43b3-a339-b027a3a3634e
-- title:
--   From a shifted quadratic decay bound to $g = O(|w|^{-2})$ at infinity
-- statement:
--   Let $g \colon \mathbb{R} \to \mathbb{C}$ and let $c, h, C$ be real constants with $h \ne 0$. Suppose the pointwise bound
--   $$\|g(w)\| \,\bigl(1 + (c - w h)^2\bigr) \;\le\; C \qquad \text{for all } w \in \mathbb{R}.$$
--   Then $g$ decays quadratically at infinity:
--   $$g(w) \;=\; O\bigl(|w|^{-2}\bigr)$$
--   along the filter `cocompact ℝ` (i.e. as $|w| \to \infty$), stated with the real power $|w|^{-2}$ (`rpow`). The proof shows that for $|w|$ large, $|c - wh| \ge |w||h|/2$, so the hypothesis forces $\|g(w)\| \le (4C/h^2)\, w^{-2}$.
--
--   In the module `Zeta23.Poisson` this converts the window decay hypothesis $|\hat\varphi(s)|(1+s^2) \le C$, evaluated along the arithmetic progression $s = \tau - (T + wh)$, into the $O(|w|^{-2})$ decay required by Mathlib's Poisson summation theorem (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`); its consumer is `Zeta23.Poisson.hasSum_paperFT_mul_paperFT`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L43-L81

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson

theorem Zeta23.Poisson.isBigO_of_decay {g : ℝ → ℂ} {c h C : ℝ} (hh : h ≠ 0)
    (hg : ∀ w, ‖g w‖ * (1 + (c - w * h) ^ 2) ≤ C) :
    g =O[cocompact ℝ] fun w : ℝ => |w| ^ (-2 : ℝ) := by sorry
