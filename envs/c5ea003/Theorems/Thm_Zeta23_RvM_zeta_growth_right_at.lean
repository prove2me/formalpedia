-- Prove2me | Theorems.Thm_Zeta23_RvM_zeta_growth_right_at
-- name    : Zeta23.RvM.zeta_growth_right_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:28.43389+00:00
-- url     : https://prove2.me/theorems/f5107120-83ac-423b-beac-9d7a993e23ba
-- title:
--   Polynomial growth of $\zeta$ to the right of $\sigma = 0.15$: $\|\zeta(s)\| \le \tfrac{20}{3}(|\operatorname{Im} s| + 3)$
-- statement:
--   For every complex $s$ with $\operatorname{Re} s \ge 0.15$ and $\|s - 1\| \ge 1$ (distance at least $1$ from the pole at $s=1$),
--   $$\|\zeta(s)\| \;\le\; \frac{20}{3}\,\bigl(|\operatorname{Im} s| + 3\bigr)^{1},$$
--   where $\zeta$ is Mathlib's `riemannZeta`. The exponent is written as the real power $(\cdot)^{(1:\mathbb{R})}$ because the statement is an explicit instance of the interface shape $\|\zeta(s)\| \le C\,(|\operatorname{Im} s| + 3)^{A}$, here realized with $A = 1$ and $C = 20/3$.
--
--   Unlike the linear-growth bound on half-planes $\operatorname{Re} s \ge \delta$ with $|\operatorname{Im} s| \ge 1$, this estimate is uniform down to small $|\operatorname{Im} s|$, requiring only that $s$ keep distance $1$ from the pole.
--
--   It is the growth input to the Jensen-type local zero count: it is consumed by `Zeta23.RvM.half_count_large` (the count of zeros in discs used for the unit-window bound) and by `Zeta23.RvM.rvM_main`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ZetaGrowth.lean#L116-L141

import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open Complex Set MeasureTheory Real

theorem Zeta23.RvM.zeta_growth_right_at (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ) := by sorry
