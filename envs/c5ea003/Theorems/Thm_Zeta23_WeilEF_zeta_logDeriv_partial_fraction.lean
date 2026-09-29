-- Prove2me | Theorems.Thm_Zeta23_WeilEF_zeta_logDeriv_partial_fraction
-- name    : Zeta23.WeilEF.zeta_logDeriv_partial_fraction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:49:57.112666+00:00
-- url     : https://prove2.me/theorems/17bc1d9d-0fcc-410c-8366-5a508c03d66d
-- title:
--   Partial-fraction expansion of $\zeta'/\zeta$ at height $t$
-- statement:
--   **Statement.** There is a constant $C > 0$ such that for every real $t$ with $|t| \ge 6$ there exists a finite set $Z \subseteq \mathbb{C}$ with the following three properties.
--   1. $Z$ consists exactly of the zeros of $\zeta$ in the closed disc of radius $\tfrac{22}{25} \cdot \tfrac{91}{50}$ centred at $2 + it$.
--   2. The total multiplicity is small: $\sum_{\rho \in Z} m_\rho \le C \log(|t| + 3)$, where $m_\rho$ is the order of vanishing of $\zeta$ at $\rho$ (`analyticOrderNatAt`).
--   3. For every $s$ in the closed disc of radius $3/2$ about $2 + it$ with $\zeta(s) \ne 0$,
--   $$\Bigl\| \frac{\zeta'}{\zeta}(s) \; - \; \sum_{\rho \in Z} \frac{m_\rho}{s - \rho} \Bigr\| \;\le\; C \log(|t| + 3).$$
--   The disc of radius $3/2$ about $2 + it$ covers the segment $1/2 \le \operatorname{Re} s \le 2$ at height $t$, so this is the classical Landau lemma: away from its nearby zeros, $\zeta'/\zeta$ equals the sum of the singular terms $m_\rho/(s - \rho)$ up to an error $O(\log |t|)$.
--
--   **Role.** In the module `Zeta23.WeilEF.Landau` (built on the Borel–Carathéodory bound `norm_logDeriv_Cf_le`) it feeds `good_heights_at`: combined with the local zero count it bounds $\zeta'/\zeta$ on zero-free horizontal segments, which control the horizontal sides of the explicit formula contour.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Landau.lean#L508-L657

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

theorem Zeta23.WeilEF.zeta_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by sorry
