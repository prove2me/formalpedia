-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_integral_inv_add_eq
-- name    : Zeta23.StirlingVert.integral_inv_add_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:52.672335+00:00
-- url     : https://prove2.me/theorems/160f2150-40db-4468-be89-a5e5d4174c72
-- title:
--   Unit-interval expansion: $\int_m^{m+1}\frac{dx}{x+w} = \frac{1}{m+w} - \frac{1}{2(m+w)^2} + \varepsilon_m$
-- statement:
--   Let $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$ and let $m \ge 0$ be real. With the per-interval remainder $\varepsilon_m(w) := \int_m^{m+1} \frac{(x-m)^2}{(m+w)^2 (x+w)}\,dx$, one has the exact identity
--   $$\int_m^{m+1} \frac{dx}{x+w} \;=\; \frac{1}{m+w} \;-\; \frac{1}{2\,(m+w)^{2}} \;+\; \varepsilon_m(w).$$
--
--   The identity comes from the exact algebraic expansion $\frac{1}{x+w} = \frac{1}{m+w} - \frac{x-m}{(m+w)^2} + \frac{(x-m)^2}{(m+w)^2(x+w)}$ integrated over $[m, m+1]$; on the other side, the integral equals $\log(m+1+w) - \log(m+w)$ by the fundamental theorem of calculus on the slit plane, so summing over $m$ telescopes. This is the elementary substitute for Euler-Maclaurin in the vertical Stirling development.
--
--   Consumers: `Zeta23.StirlingVert.partial_sum_eq` (the rearranged partial sums of the digamma series) and `Zeta23.StirlingVert.digamma_stirling` (the Stirling estimate for $\psi$).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L97-L133

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

theorem Zeta23.StirlingVert.integral_inv_add_eq {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by sorry
