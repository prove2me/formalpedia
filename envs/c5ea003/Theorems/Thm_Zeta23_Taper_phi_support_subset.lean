-- Prove2me | Theorems.Thm_Zeta23_Taper_phi_support_subset
-- name    : Zeta23.Taper.phi_support_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:09.799769+00:00
-- url     : https://prove2.me/theorems/f830869e-c4f9-44d6-89b5-c7eb3ab17c99
-- title:
--   Support of the taper: $\operatorname{supp}\varphi \subseteq [-L/2,\ L/2]$
-- statement:
--   Let $\varrho$ be a taper profile (nondecreasing, $C^3$, vanishing on $(-\infty,0]$, equal to $1$ on $[1,\infty)$), let $w > 0$, and let $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ be the taper of [eq:phidef].
--
--   The theorem asserts the support inclusion
--   $$\operatorname{supp}\varphi \;\subseteq\; \left[-\frac{L}{2},\ \frac{L}{2}\right],$$
--   since for $|u| \ge L/2$ the argument $(L/2-|u|)/w$ is nonpositive and hence $\varrho$ vanishes there.
--
--   This is a basic structural fact from the sentence after [eq:phidef] ("$\operatorname{supp}\varphi = [-L/2, L/2]$"; the formalization proves the inclusion, which is what is used). It underlies compact-support and $L^1$ arguments throughout the taper development — consumers include `integral_phi_le`, `norm_phiHat_le`, `aConst_le_one`, `bConst_le_aConst`, `one_sub_le_bConst`, the Fourier evaluations `integral_PhiR_sq_mul_cos` / `integral_phiHatR_sq_mul_cos`, and the assembly nodes `Zeta23.PrimeSide.localHyps_concrete` and `Zeta23.eventually_side_conditions`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Basic.lean#L132-L141

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

theorem Zeta23.Taper.phi_support_subset (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    Function.support (phi ϱ L w) ⊆ Icc (-(L / 2)) (L / 2) := by sorry
