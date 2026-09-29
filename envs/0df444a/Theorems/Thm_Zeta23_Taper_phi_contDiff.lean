-- Prove2me | Theorems.Thm_Zeta23_Taper_phi_contDiff
-- name    : Zeta23.Taper.phi_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:04.226055+00:00
-- url     : https://prove2.me/theorems/46ea59bc-58ef-4c75-94c8-3e7fb5a5c2d7
-- title:
--   Smoothness of the taper: $\varphi \in C^3(\mathbb{R})$
-- statement:
--   Let $\varrho$ be a taper profile — a nondecreasing $C^3$ function on $\mathbb{R}$ with $\varrho = 0$ on $(-\infty,0]$ and $\varrho = 1$ on $[1,\infty)$ — and let $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ be the taper of [eq:phidef], with $0 < w$ and $2w \le L$.
--
--   The theorem asserts that $\varphi$ is three times continuously differentiable:
--   $$\varphi \in C^3(\mathbb{R}).$$
--   Despite the $|u|$ in the definition, smoothness holds because of the product form `phi_eq_mul`: when $2w \le L$, $\varphi(u) = \varrho\big((L/2-u)/w\big)\,\varrho\big((L/2+u)/w\big)$, a product of $C^3$ functions. Combined with compact support this gives the paper's "$\varphi \in C_c^3(\mathbb{R})$".
--
--   This is the foundational regularity fact of the taper family [subsec:family]: essentially every analytic statement about $\varphi$ in the project depends on it, including the norm computations of [eq:phinorms] (`integral_abs_deriv_phi`, `integral_abs_deriv2_phi`, ...), the transform bounds of [eq:hfbound] (`norm_phiHat_le`, `abs_phiHatR_mul_abs_le`, `abs_PhiR_mul_sq_le`, ...), the Fourier identities (`integral_PhiR_sq_mul_cos`, `hasSum_phiHatR_mul`), the constants $a, b$ of [eq:abdef] (`aConst_le_one`, `bConst_le_aConst`, `one_sub_le_bConst`), and the assembly nodes `Zeta23.PrimeSide.localHyps_concrete`, `Zeta23.Tail.eventually_tailPackage` and `Zeta23.eventually_side_conditions`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Basic.lean#L160-L168

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
variable (ϱ : ℝ → ℝ) (L w : ℝ)
variable {ϱ L w}

theorem Zeta23.Taper.phi_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 3 (phi ϱ L w) := by sorry
