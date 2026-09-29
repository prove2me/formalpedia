-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_phi_le
-- name    : Zeta23.Taper.integral_phi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:25.941128+00:00
-- url     : https://prove2.me/theorems/59233f7c-4512-47f3-b898-e6bebaedbd8c
-- title:
--   Elementary mass bound for the taper: $\int_{\mathbb{R}} \varphi \le L$
-- statement:
--   Let $\varrho$ be a taper profile (nondecreasing, $C^3$, $\varrho = 0$ on $(-\infty,0]$, $\varrho = 1$ on $[1,\infty)$) and let $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ be the associated taper with support length $L$ and ramp width $w$, where $0 < w$ and $2w \le L$.
--
--   The theorem asserts the elementary bound
--   $$\int_{\mathbb{R}} \varphi(u)\,du \;\le\; L,$$
--   which follows from $0 \le \varphi \le 1$ together with $\operatorname{supp}\varphi \subseteq [-L/2, L/2]$.
--
--   Within the project this bound feeds the trivial sup-norm estimates for the transforms of $\varphi$: it is used in `Zeta23.Taper.norm_phiHat_le` (the zeroth-order bound $\|\hat\varphi(z)\| \le e^{|\operatorname{Im} z|L/2} L$) and in `Zeta23.Taper.abs_PhiR_le_L`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Strip.lean#L64-L82

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
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.integral_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, phi ϱ L w u ≤ L := by sorry
