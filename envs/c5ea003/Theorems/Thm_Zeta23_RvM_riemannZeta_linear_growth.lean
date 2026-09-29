-- Prove2me | Theorems.Thm_Zeta23_RvM_riemannZeta_linear_growth
-- name    : Zeta23.RvM.riemannZeta_linear_growth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:40.462043+00:00
-- url     : https://prove2.me/theorems/7e9a1251-3834-4fa2-9b09-a673b1858d26
-- title:
--   Linear growth of $\zeta$ in every right half-plane $\operatorname{Re} s \ge \delta > 0$
-- statement:
--   Let $\delta > 0$ and let $s$ be a complex number with $\operatorname{Re} s \ge \delta$ and $|\operatorname{Im} s| \ge 1$. Then the Riemann zeta function (Mathlib's `riemannZeta`) satisfies the fully explicit linear bound
--   $$\|\zeta(s)\| \;\le\; \Bigl(\frac{5}{2} + \delta^{-1}\Bigr)\,|\operatorname{Im} s|.$$
--
--   The point is uniformity: a single explicit constant depending only on the distance $\delta$ to the imaginary axis controls $\zeta$ linearly in the height, throughout the half-plane $\operatorname{Re} s \ge \delta$ away from the real axis.
--
--   In the project this growth estimate feeds `Zeta23.WeilEF.zeta_logDeriv_partial_fraction`, the partial-fraction expansion of $\zeta'/\zeta$ over the nontrivial zeros used in the Weil-type explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ZetaGrowth.lean#L76-L98

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

theorem Zeta23.RvM.riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im| := by sorry
