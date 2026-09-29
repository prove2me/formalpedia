-- Prove2me | Theorems.Thm_Zeta23_Taper_continuous_paperFT_ofReal
-- name    : Zeta23.Taper.continuous_paperFT_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:14.690273+00:00
-- url     : https://prove2.me/theorems/22dcb7e6-0e31-41e1-86c7-f29938ea033d
-- title:
--   Continuity of $h_f$ on $\mathbb{R}$ for integrable $f$
-- statement:
--   The paper's Fourier transform of $f : \mathbb{R} \to \mathbb{C}$ is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`).
--
--   Suppose $f$ is (Bochner) integrable on $\mathbb{R}$. Then the restriction of $h_f$ to the real line, $r \mapsto h_f(r)$, is continuous, by dominated convergence with the constant dominating bound $\|f\|_1$.
--
--   This is the auxiliary continuity statement kept in `Zeta23.Taper.Decay` (the downstream module `Zeta23.Taper.Fourier` carries the specialized `phiHatR_continuous`); it is consumed by `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L533-L545

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

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.continuous_paperFT_ofReal {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun r : ℝ => paperFT f r) := by sorry
