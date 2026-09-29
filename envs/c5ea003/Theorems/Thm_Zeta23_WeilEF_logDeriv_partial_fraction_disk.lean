-- Prove2me | Theorems.Thm_Zeta23_WeilEF_logDeriv_partial_fraction_disk
-- name    : Zeta23.WeilEF.logDeriv_partial_fraction_disk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:49:56.779906+00:00
-- url     : https://prove2.me/theorems/536dcf62-842b-4a5b-be8f-1e3bac245a08
-- title:
--   Landau partial-fraction expansion of $f'/f$ on a general disk
-- statement:
--   Setup. Let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed ball $\overline{B}(s_0, R)$ with $R > 0$ and $f(s_0) \ne 0$. Assume the growth bound: for some $B \ge 2$,
--   $$\|f(w)\| \;\le\; B\,\|f(s_0)\| \qquad \text{for all } w \in \overline{B}\bigl(s_0, \tfrac{24}{25}R\bigr).$$
--   Here $m_\rho = \operatorname{analyticOrderNatAt} f\,\rho$ denotes the (finite, $\mathbb{N}$-valued) order of vanishing of $f$ at $\rho$.
--
--   Assertion. There is a finite set $Z \subset \mathbb{C}$ such that:
--
--   1. $Z$ is exactly the zero set of $f$ in the closed ball $\overline{B}(s_0, \tfrac{22}{25}R)$;
--   2. the total multiplicity is logarithmically bounded:
--   $$\sum_{\rho \in Z} m_\rho \;\le\; \frac{\log B}{\log(12/11)}\,;$$
--   3. for every $s \in \overline{B}(s_0, \tfrac{83}{100}R)$ with $f(s) \ne 0$, the logarithmic derivative is the zero sum up to an explicit error:
--   $$\Bigl\|\frac{f'}{f}(s) \;-\; \sum_{\rho \in Z} \frac{m_\rho}{s - \rho}\Bigr\| \;\le\; \frac{44795000}{R}\,\log B.$$
--
--   This is the classical Landau lemma, obtained from the unit-disk version by affine rescaling; the explicit numerical constant is what the formalization actually certifies. It is consumed by `zeta_logDeriv_partial_fraction`, the specialization to $\zeta$ that drives the good-heights bound on $\zeta'/\zeta$ used in the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L344-L503

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open Complex Set
open Metric

theorem Zeta23.WeilEF.logDeriv_partial_fraction_disk {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B := by sorry
