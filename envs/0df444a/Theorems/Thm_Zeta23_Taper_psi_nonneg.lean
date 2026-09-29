-- Prove2me | Theorems.Thm_Zeta23_Taper_psi_nonneg
-- name    : Zeta23.Taper.psi_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:18.510501+00:00
-- url     : https://prove2.me/theorems/e1a185ee-249e-4bef-8116-6c60a1e149cf
-- title:
--   Nonnegativity of the decay majorant: $0 \le \psi$
-- statement:
--   Let $\varrho$ be a taper profile with constant $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ ($\ge 4$), and let $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ for $r \ne 0$, $\psi(0) := L$, be the decay majorant of [eq:psidef].
--
--   Assuming $1 \le w$ and $2 w \le L$ (so in particular $L \ge 2$), the theorem asserts
--   $$0 \;\le\; \psi(r) \qquad \text{for every } r \in \mathbb{R},$$
--   since each of the three entries of the minimum is nonnegative under these hypotheses.
--
--   In the project this positivity is used throughout the $\psi$-moment computations of [eq:psiints] — `integral_psi_Ioi_le`, `integral_psi_sq_le`, `integral_psi_sq_mul_abs_le`, `psi_sq_integrable`, `psi_sq_mul_abs_integrable` — and in `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L389-L396

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
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.psi_nonneg (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    0 ≤ psi ϱ L w r := by sorry
