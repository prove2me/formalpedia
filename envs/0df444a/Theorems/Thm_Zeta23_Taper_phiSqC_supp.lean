-- Prove2me | Theorems.Thm_Zeta23_Taper_phiSqC_supp
-- name    : Zeta23.Taper.phiSqC_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:13.353527+00:00
-- url     : https://prove2.me/theorems/35b2b270-db72-427b-ba06-179bccedcf14
-- title:
--   Support of $\varphi^2$: nonvanishing forces $|u| \le L/2$
-- statement:
--   Let $\varrho$ be a taper profile and $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ the taper of [eq:phidef] with ramp width $w > 0$.
--
--   The theorem asserts that the complexification of $\varphi^2$ is supported in $[-L/2, L/2]$: for every $u \in \mathbb{R}$, if $\big(\varphi(u)^2 : \mathbb{C}\big) \ne 0$ then $|u| \le L/2$. This is the support statement for $\varphi^2$ in exactly the form (a hypothesis about the complex-valued function) required by the transform-decay lemmas such as `norm_paperFT_mul_le`.
--
--   In the project it is consumed by `Zeta23.Taper.integral_PhiR_sq_mul_cos` (Fourier evaluation for $\Phi = (\varphi^2)^{\wedge}$) and by `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L314-L321

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
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.phiSqC_supp (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (((phi ϱ L w u) ^ 2 : ℝ) : ℂ) ≠ 0 → |u| ≤ L / 2 := by sorry
