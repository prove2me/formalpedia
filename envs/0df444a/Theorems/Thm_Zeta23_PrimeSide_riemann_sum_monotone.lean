-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_riemann_sum_monotone
-- name    : Zeta23.PrimeSide.riemann_sum_monotone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:26:12.607833+00:00
-- url     : https://prove2.me/theorems/6a76cccc-cd2d-4fd3-ac16-c07be4cec0b5
-- title:
--   Riemann sums of a monotone function: $h \sum_{k<\lfloor T/h\rfloor} \mu(T + kh) = \int_T^{2T} \mu + O(h\,\mu(2T))$
-- statement:
--   **Setup.** Let $\mu : \mathbb{R} \to \mathbb{R}$ be an arbitrary function (here a generic integrand, not specifically the archimedean density), let $T, h \in \mathbb{R}$ with $0 < h \le T$, and write $d = \lfloor T/h \rfloor$ (natural-number floor). Assume $\mu$ is monotone (non-decreasing) on $[T - h, \infty)$ and non-negative there.
--
--   **Statement.**
--   $$\left|\, h \sum_{k=0}^{d-1} \mu(T + k h) \;-\; \int_T^{2T} \mu(x)\, dx \,\right| \le 2\, h\, \mu(2T).$$
--   This rescales Mathlib's unit-step Riemann-sum estimates for monotone functions to step $h$ and combines them, using that the grid satisfies $T < T + dh \le 2T < T + (d+1)h$ (§5.2).
--
--   **Role.** Used in `Zeta23.PrimeSide.prop_trace_mu` to convert the grid sum $h\sum_{k<d} \mu(\tau_k)$ arising from the diagonal entries of the prime-side matrix into the integral $\int_T^{2T} \mu$, at the acceptable cost $O(h\,\mu(2T))$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L877-L982

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

theorem Zeta23.PrimeSide.riemann_sum_monotone {μ : ℝ → ℝ} {T h : ℝ} (hh : 0 < h) (hhT : h ≤ T)
    (hmono : MonotoneOn μ (Set.Ici (T - h))) (hnonneg : ∀ x, T - h ≤ x → 0 ≤ μ x) :
    |h * ∑ k ∈ Finset.range ⌊T / h⌋₊, μ (T + k * h) - ∫ x in T..(2 * T), μ x|
      ≤ 2 * h * μ (2 * T) := by sorry
