-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_PX_abs_le
-- name    : Zeta23.PrimeSide.PX_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:05:59.701482+00:00
-- url     : https://prove2.me/theorems/7b4bf015-6648-4ed5-865e-597156779095
-- title:
--   Uniform bound $|P_X(\tau)| \le \sqrt X$ for all large $X$
-- statement:
--   Here $P_X(\tau) = -\tfrac1\pi\sum_{n \le X}\Lambda(n)\,n^{-1/2}\cos(\tau\log n)$ is the prime-power density [eq:Pdef], and `ChebyshevMertens` is the hypothesis H-cheb [lem:cheb], whose second clause [eq:cheb1] provides $\sum_{n\le x}\Lambda(n)/\sqrt n \le 3\sqrt x$ for $x \ge x_0$.
--
--   The theorem asserts: assuming H-cheb, there exists a threshold $x_0$ such that for every $X \ge x_0$ and every real $\tau$,
--   $$|P_X(\tau)| \;\le\; \sqrt X.$$
--   Indeed the triangle inequality gives $|P_X(\tau)| \le \tfrac1\pi\sum_{n\le X}\Lambda(n)/\sqrt n \le \tfrac3\pi\sqrt X \le \sqrt X$ — the second half of [eq:PiPfacts] (§2.1), used in the form "$|P_X| \le \sqrt X$" at §5.4.
--
--   It is consumed by `prop_cross_PPi`, the estimate of the $P \times \Pi$ cross term in the second moment.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L688-L713, docstring tags [eq:cheb1], [eq:PiPfacts]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.PX_abs_le (hcheb : Zeta23.ChebyshevMertens) :
    ∃ x₀ : ℝ, ∀ X, x₀ ≤ X → ∀ τ, |Zeta23.PX X τ| ≤ Real.sqrt X := by sorry
