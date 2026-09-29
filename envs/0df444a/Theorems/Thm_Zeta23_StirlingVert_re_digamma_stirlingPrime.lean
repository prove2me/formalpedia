-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirlingPrime
-- name    : Zeta23.StirlingVert.re_digamma_stirlingPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:54.301469+00:00
-- url     : https://prove2.me/theorems/3bf30d61-c26a-48c9-9952-e2806f013973
-- title:
--   Real part of $\psi$ with $\log|t|$ main term: error $\le 5/t^2$
-- statement:
--   Let $a$ be real with $0 < a \le 1$ and let $t$ be real with $|t| \ge 1/2$. Then
--   $$\bigl|\,\operatorname{Re}\,\psi(a + it) \;-\; \log|t|\,\bigr| \;\le\; \frac{5}{t^{2}},$$
--   where $\psi$ is `Complex.digamma`.
--
--   This sharpens `re_digamma_stirling` by replacing the main term $\tfrac12\log(a^2+t^2)$ with the simpler $\log|t|$: the swap costs $\tfrac12\log(1 + a^2/t^2) \le a^2/(2t^2) \le \tfrac12 t^{-2}$, so the error constant moves from $4$ to $5$ (the source notes the intermediate bound $(4 + a^2/2)/t^2$).
--
--   Its sole consumer is `Zeta23.StirlingVert.mu_stirling`: evaluating at $a = 1/4$, $t = \tau/2$ and dividing by $2\pi$ yields the H-$\Gamma$ Stirling clause $\mu(\tau) = \frac{1}{2\pi}\log\frac{|\tau|}{2\pi} + O(\tau^{-2})$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L587-L612

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert

open Zeta23
open StirlingVert
open Complex Filter Topology MeasureTheory intervalIntegral Set

theorem Zeta23.StirlingVert.re_digamma_stirlingPrime {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by sorry
