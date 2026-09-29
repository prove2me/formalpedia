-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_norm_eps_le
-- name    : Zeta23.StirlingVert.norm_eps_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:46.551708+00:00
-- url     : https://prove2.me/theorems/215a8f3f-55e1-41a7-86d4-2ac6ffb490b4
-- title:
--   Remainder bound: $\|\varepsilon_m(w)\| \le \dfrac{1}{3\,\|m+w\|^2\,|\operatorname{Im} w|}$
-- statement:
--   Let $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$ and $|\operatorname{Im} w| \ge 1/2$, and let $m \ge 0$ be real. The per-interval remainder $\varepsilon_m(w) := \int_m^{m+1} \frac{(x-m)^2}{(m+w)^2(x+w)}\,dx$ of the vertical Stirling development satisfies
--   $$\|\varepsilon_m(w)\| \;\le\; \frac{1}{3\,\|m+w\|^{2}\,|\operatorname{Im} w|}.$$
--
--   The bound uses $\int_m^{m+1}(x-m)^2\,dx = \tfrac13$ together with $|x+w| \ge |\operatorname{Im} w|$ pointwise; the resulting decay in $m$ (like $\|m+w\|^{-2}$) makes the series $\sum_m \varepsilon_m(w)$ absolutely convergent, with total mass $O(1/(\operatorname{Im} w)^2)$ after summation.
--
--   Consumers: `Zeta23.StirlingVert.digamma_eq` (convergence of the remainder series in the exact digamma formula) and `Zeta23.StirlingVert.digamma_stirling` (the final error estimate $\le 3/(\operatorname{Im} w)^2$).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L135-L165

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

theorem Zeta23.StirlingVert.norm_eps_le {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by sorry
