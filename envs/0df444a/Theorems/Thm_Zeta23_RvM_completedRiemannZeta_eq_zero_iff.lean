-- Prove2me | Theorems.Thm_Zeta23_RvM_completedRiemannZeta_eq_zero_iff
-- name    : Zeta23.RvM.completedRiemannZeta_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:43.711799+00:00
-- url     : https://prove2.me/theorems/d75e1c1a-c6f3-4abb-b1d5-aaf846bb5c10
-- title:
--   Zeros of the completed zeta $\Lambda$ are exactly the nontrivial zeros of $\zeta$
-- statement:
--   **Setup.** $\Lambda$ denotes Mathlib's `completedRiemannZeta`, the completed Riemann zeta function $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ (extended by Mathlib across its poles at $s = 0, 1$ with finite ''junk'' values). `IsNontrivialZero s` means $\zeta(s) = 0$ and $0 < \mathrm{Re}\, s < 1$.
--
--   **Statement.** For every complex number $s$:
--
--   $$\Lambda(s) = 0 \iff \zeta(s) = 0 \ \text{ and } \ 0 < \mathrm{Re}\, s < 1.$$
--
--   The equivalence holds at *every* $s$, with no restriction to the critical strip: outside the strip $\Lambda$ does not vanish (the $\Gamma$-factor's poles cancel the trivial zeros of $\zeta$, and $\zeta$ has no zeros with $\mathrm{Re}\,s \ge 1$ or, by the functional equation, $\mathrm{Re}\,s \le 0$ other than the trivial ones), and at the exceptional points $s = 0, 1$ Mathlib's junk values are nonzero as well, since $\Lambda(0) = \Lambda(1)$ and $\zeta(1) \ne 0$ under Mathlib's conventions.
--
--   **Role.** In `Zeta23.RvM.CountByIntegral` this identifies the zero set of the entire-away-from-poles function $\Lambda$, to which the argument principle is applied, with the nontrivial zeros being counted. It feeds `Zeta23.RvM.horizontal_fold` and `Zeta23.RvM.rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/CountByIntegral.lean#L63-L77

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

open Complex Set Topology Filter Real
open Zeta23

theorem Zeta23.RvM.completedRiemannZeta_eq_zero_iff {s : ℂ} :
    completedRiemannZeta s = 0 ↔ IsNontrivialZero s := by sorry
