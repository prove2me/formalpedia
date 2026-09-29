-- Prove2me | Theorems.Thm_Zeta23_MuFields_re_digamma_vertical
-- name    : Zeta23.MuFields.re_digamma_vertical
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:15.619873+00:00
-- url     : https://prove2.me/theorems/81c4a2e9-688d-439d-81ac-a2fb196605ac
-- title:
--   Digamma series for $\mathrm{Re}\,\psi(a+it)$ on vertical lines
-- statement:
--   Fix a real abscissa $a$ with $0 < a < 1$, and let $\psi = \Gamma'/\Gamma$ be the digamma function (Mathlib's `Complex.digamma`) and $\gamma$ the Euler–Mascheroni constant. For every real $t$,
--   $$\mathrm{Re}\,\psi(a + it) \;=\; -\gamma \;-\; \frac{a}{a^2 + t^2} \;+\; \sum_{n=0}^{\infty} \Bigl( \frac{1}{n+1} \;-\; \frac{n+1+a}{(n+1+a)^2 + t^2} \Bigr),$$
--   where the sum is a `tsum` over $n \in \mathbb{N}$. This is the display in the paper's [eq:mufacts] ("$\mathrm{Re}\,\Gamma'/\Gamma(\sigma+it) = -\gamma_E + \sum_{n\ge 0}(1/(n+1) - (n+\sigma)/((n+\sigma)^2+t^2))$"), obtained by taking real parts in the classical digamma series.
--
--   This identity is the analytic foundation of the module `Zeta23.GammaFacts.Mu`: its consumers are `Zeta23.MuFields.neg_one_lt_mu_zero` (the bound $\mu(0) > -1$) and `Zeta23.MuFields.re_digamma_mono` (monotonicity in $t$), which in turn drive the H-$\Gamma$ facts about the density $\mu$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L77-L101, docstring tag [eq:mufacts]

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

theorem Zeta23.MuFields.re_digamma_vertical (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2)
        + ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by sorry
