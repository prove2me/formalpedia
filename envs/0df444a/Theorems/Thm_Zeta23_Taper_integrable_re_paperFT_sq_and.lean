-- Prove2me | Theorems.Thm_Zeta23_Taper_integrable_re_paperFT_sq_and
-- name    : Zeta23.Taper.integrable_re_paperFT_sq_and
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:33:29.072606+00:00
-- url     : https://prove2.me/theorems/3ba5909d-b853-4435-be6c-66c87ea0d499
-- title:
--   Integrability of $(\operatorname{Re} h_f)^2$ and $(\operatorname{Re} h_f)^2\,|r|$ for $f \in C_c^2$
-- statement:
--   The paper's Fourier transform of $f : \mathbb{R} \to \mathbb{C}$ is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`).
--
--   Suppose $f$ is $C^2$ and supported in $[-\Lambda, \Lambda]$ (formally: $f(u) \ne 0$ implies $|u| \le \Lambda$). Then both
--
--   $$r \mapsto \bigl(\operatorname{Re} h_f(r)\bigr)^2 \qquad\text{and}\qquad r \mapsto \bigl(\operatorname{Re} h_f(r)\bigr)^2\,|r|$$
--
--   are integrable on $\mathbb{R}$. The proof uses the decay estimates [eq:hfbound], $|h_f(r)| \le \|f\|_1$ and $|h_f(r)|\,r^2 \le \|f''\|_1$, so the square decays like $r^{-4}$ at infinity.
--
--   This integrability underlies the Fourier-inversion identities for $\hat\varphi^2$ and $\Phi^2$ (`integral_phiHatR_sq_mul_cos`, `integral_PhiR_sq_mul_cos`) and is consumed by `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L109-L159, docstring tag [eq:hfbound]

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
open scoped FourierTransform ComplexConjugate
open Zeta23
variable {v : ℝ → ℝ}

theorem Zeta23.Taper.integrable_re_paperFT_sq_and {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun r : ℝ => (paperFT f r).re ^ 2) ∧
      Integrable (fun r : ℝ => (paperFT f r).re ^ 2 * |r|) := by sorry
