-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirling
-- name    : Zeta23.StirlingVert.re_digamma_stirling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:48.781188+00:00
-- url     : https://prove2.me/theorems/a36cc46a-c4c1-44bb-8cc7-5fcc1d618a1e
-- title:
--   Real part of $\psi$ on vertical lines: $\bigl|\operatorname{Re}\psi(a+it) - \tfrac12\log(a^2+t^2)\bigr| \le 4/t^2$
-- statement:
--   Let $a$ be real with $0 < a \le 1$ and let $t$ be real with $|t| \ge 1/2$. Then the real part of the digamma function on the vertical line $\operatorname{Re} = a$ satisfies
--   $$\Bigl|\,\operatorname{Re}\,\psi(a + it) \;-\; \frac{1}{2}\,\log\bigl(a^{2} + t^{2}\bigr)\,\Bigr| \;\le\; \frac{4}{t^{2}},$$
--   where $\psi$ is `Complex.digamma` and the argument is written $a + i t$ in Lean as $(a : \mathbb{C}) + I\,t$.
--
--   This follows by taking real parts in the complex Stirling estimate `digamma_stirling`: $\operatorname{Re}\log w = \log\|w\| = \tfrac12\log(a^2+t^2)$, while $|\operatorname{Re}\frac{1}{2w}| = \frac{a}{2(a^2+t^2)} \le \frac{1}{2t^2}$, which together with the $3/t^2$ error gives the constant $4$.
--
--   Its sole consumer is `Zeta23.StirlingVert.re_digamma_stirlingPrime`, the variant with $\log|t|$ as the main term, en route to the Stirling clause for the density $\mu$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L548-L585

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

theorem Zeta23.StirlingVert.re_digamma_stirling {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
      ≤ 4 / t ^ 2 := by sorry
