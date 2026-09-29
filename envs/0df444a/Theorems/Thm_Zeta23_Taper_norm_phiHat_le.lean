-- Prove2me | Theorems.Thm_Zeta23_Taper_norm_phiHat_le
-- name    : Zeta23.Taper.norm_phiHat_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:53.455951+00:00
-- url     : https://prove2.me/theorems/f843bb36-b6a2-48ec-a013-2f957d8dbd9e
-- title:
--   Zeroth-order strip bound for $\hat\varphi$: $\|\hat\varphi(z)\| \le e^{|\mathrm{Im}\,z|\,L/2}\, L$
-- statement:
--   Let $\varrho$ be a taper profile and $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ the taper of [eq:phidef] with $0 < w$ and $2w \le L$. Let $\hat\varphi(z) := \int_{\mathbb{R}} \varphi(u)\,e^{izu}\,du$ be its paper Fourier transform, defined for all complex $z$.
--
--   The theorem asserts, for every $z \in \mathbb{C}$,
--   $$\|\hat\varphi(z)\| \;\le\; e^{|\operatorname{Im} z| \cdot L/2}\, L.$$
--   This is the zeroth-order instance of [eq:hfbound] for $\varphi$: since $\operatorname{supp}\varphi \subseteq [-L/2, L/2]$, one has $|e^{izu}| \le e^{|\operatorname{Im} z| L/2}$ on the support, and $\|\varphi\|_1 \le L$ (from `integral_phi_le`).
--
--   In the project this trivial strip bound is used by `Zeta23.Taper.hasSum_phiHatR_mul` (summability of zero sums against $\hat\varphi$) and by `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Strip.lean#L84-L94, docstring tag [eq:hfbound]

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

theorem Zeta23.Taper.norm_phiHat_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (z : ℂ) :
    ‖phiHat ϱ L w z‖ ≤ Real.exp (|z.im| * (L / 2)) * L := by sorry
