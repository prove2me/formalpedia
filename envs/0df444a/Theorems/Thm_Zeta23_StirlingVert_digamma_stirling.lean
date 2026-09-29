-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_digamma_stirling
-- name    : Zeta23.StirlingVert.digamma_stirling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:42.497976+00:00
-- url     : https://prove2.me/theorems/0d2e50fb-fdc7-47be-ad04-d41bc947a65c
-- title:
--   Stirling for $\psi$ on the right half-plane: $\bigl\|\psi(w) - \log w + \tfrac{1}{2w}\bigr\| \le 3/(\operatorname{Im} w)^2$
-- statement:
--   For every complex $w$ with $\operatorname{Re} w > 0$ and $|\operatorname{Im} w| \ge 1/2$, the digamma function $\psi = \Gamma'/\Gamma$ (Mathlib's `Complex.digamma`) satisfies the explicit Stirling estimate
--   $$\Bigl\|\,\psi(w) \;-\; \log w \;+\; \frac{1}{2w}\,\Bigr\| \;\le\; \frac{3}{(\operatorname{Im} w)^{2}},$$
--   with $\log$ the principal branch.
--
--   This is the quantitative vertical-line form of Stirling's formula for $\Gamma'/\Gamma$: the error is controlled purely by the *imaginary part* of $w$, uniformly in the real part throughout the right half-plane, which is exactly what is needed on vertical strips. It is derived from the exact identity `digamma_eq` by bounding the remainder series $\sum \rho_n$ and $\sum \varepsilon_m$.
--
--   Consumers: `Zeta23.StirlingVert.re_digamma_stirling` (its real-part specialization, en route to the H-$\Gamma$ Stirling clause for $\mu$) and `Zeta23.WeilEF.digamma_growth_strip` (digamma growth on vertical strips in the explicit-formula argument).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L481-L540

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
variable {w : ℂ}

theorem Zeta23.StirlingVert.digamma_stirling (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by sorry
