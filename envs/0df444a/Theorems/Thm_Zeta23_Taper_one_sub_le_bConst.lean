-- Prove2me | Theorems.Thm_Zeta23_Taper_one_sub_le_bConst
-- name    : Zeta23.Taper.one_sub_le_bConst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:57.205425+00:00
-- url     : https://prove2.me/theorems/1a57e502-9bad-4bab-92cd-7b4853bb01d9
-- title:
--   Plateau lower bound for $b = L^{-1}\!\int\varphi^4$: $\;1 - 2w/L \le b$
-- statement:
--   Let $\varrho$ be a taper profile and $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ the taper of [eq:phidef], with $0 < w$ and $2w \le L$. Following [eq:abdef], set
--   $$b \;:=\; L^{-1}\int_{\mathbb{R}} \varphi(u)^4\,du.$$
--
--   The theorem asserts the lower bound
--   $$1 - \frac{2w}{L} \;\le\; b.$$
--   It follows from $\varphi = 1$ on the plateau $[-L/2+w,\ L/2-w]$ (of length $L - 2w$) together with $\varphi^4 \ge 0$.
--
--   In the project this shows $b \to 1$ as the ramps become negligible ($w/L \to 0$), which is how the taper constants enter the final optimization: it is consumed by `Zeta23.PrimeSide.localHyps_concrete`, `Zeta23.Tail.eventually_tailPackage`, `Zeta23.eventually_blockInputs` and `Zeta23.eventually_side_conditions` — the nodes assembling the asymptotic side conditions as $T \to \infty$ for the matrix-variational bound behind Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L578-L608

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
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

theorem Zeta23.Taper.one_sub_le_bConst (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    1 - 2 * w / L ≤ bConst ϱ L w := by sorry
