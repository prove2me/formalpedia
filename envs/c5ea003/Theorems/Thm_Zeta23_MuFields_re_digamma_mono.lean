-- Prove2me | Theorems.Thm_Zeta23_MuFields_re_digamma_mono
-- name    : Zeta23.MuFields.re_digamma_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:16.070814+00:00
-- url     : https://prove2.me/theorems/df25f54a-1d36-4a8d-bef8-75d08a273a57
-- title:
--   Monotonicity of $\mathrm{Re}\,\psi(a+it)$ in $t \ge 0$
-- statement:
--   Fix a real abscissa $a$ with $0 < a < 1$, and let $\psi = \Gamma'/\Gamma$ denote the digamma function (Mathlib's `Complex.digamma`). The theorem asserts that the real part of $\psi$ along the vertical line $\mathrm{Re} = a$ is monotone in the height:
--   $$t \;\longmapsto\; \mathrm{Re}\,\psi(a + it) \quad \text{is monotone (non-decreasing) on } [0,\infty),$$
--   stated as `MonotoneOn` on `Set.Ici 0`. The proof works termwise in the series representation of $\mathrm{Re}\,\psi(a+it)$: each summand $\frac{1}{n+1} - \frac{n+1+a}{(n+1+a)^2+t^2}$ is increasing in $t^2$.
--
--   The abscissa is kept as a parameter $a \in (0,1)$ so the toolkit covers both $\zeta$'s case $a = 1/4$ and the shifted case needed elsewhere. Its consumer is `Zeta23.MuFields.mu_monotoneOn`, the monotonicity of the density $\mu$ in the module `Zeta23.GammaFacts.Mu`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L105-L127

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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Complex Filter Topology
variable {a : ℝ}

theorem Zeta23.MuFields.re_digamma_mono (ha0 : 0 < a) (ha1 : a < 1) :
    MonotoneOn (fun t : ℝ => (Complex.digamma ((a : ℂ) + Complex.I * t)).re)
      (Set.Ici (0 : ℝ)) := by sorry
