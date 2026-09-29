-- Prove2me | Theorems.Thm_Zeta23_MuFields_re_term_eq
-- name    : Zeta23.MuFields.re_term_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:05.516658+00:00
-- url     : https://prove2.me/theorems/0988a784-ab38-441e-9e05-baea73ff3f47
-- title:
--   Real part of the $n$-th digamma series term on the line $\mathrm{Re} = a$
-- statement:
--   Fix a real abscissa $a$ (in applications $0 < a < 1$), and let $t$ be real and $n$ a natural number. The theorem computes the real part of the $n$-th term of the digamma series at the point $a + it$:
--   $$\mathrm{Re}\Bigl( \frac{1}{n+1} \;-\; \frac{1}{(a + it) + n + 1} \Bigr) \;=\; \frac{1}{n+1} \;-\; \frac{n+1+a}{(n+1+a)^2 + t^2}.$$
--   This is a direct computation: the real part of $1/z$ is $\mathrm{Re}(z)/|z|^2$, applied with $z = (n+1+a) + it$.
--
--   It is the termwise ingredient for the series identity `Zeta23.MuFields.re_digamma_vertical` and the monotonicity statement `Zeta23.MuFields.re_digamma_mono` in the module `Zeta23.GammaFacts.Mu`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L40-L57

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

theorem Zeta23.MuFields.re_term_eq (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (((a : ℂ) + Complex.I * t) + n + 1)).re
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by sorry
