-- Prove2me | Theorems.Thm_Zeta23_RvM_rvM_main_param
-- name    : Zeta23.RvM.rvM_main_param
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:14.093298+00:00
-- url     : https://prove2.me/theorems/759fe759-611b-43af-af23-969d7f841469
-- title:
--   Riemann-von Mangoldt main term, parametric in all five constants
-- statement:
--   This is the workhorse form of the Riemann-von Mangoldt formula, in which every constant source is an explicit parameter, so that numeric inputs yield a numeric final constant. Notation: $N(T,2T)$ (`zetaZeroConfig.N T (2T)`) counts nontrivial zeros of $\zeta$ with imaginary part in $(T, 2T]$ with multiplicity; $N(t, t+1)$ (`Ncount`) is the unit-window count; $\ell_1(T) = \log\frac{T}{2\pi} + 2\log 2 - 1$; and $\mu(\tau) = \frac{1}{2\pi}\operatorname{Re}\psi(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log\pi}{2\pi}$ is the archimedean density.
--
--   **Hypotheses** (five constant sources):
--   1. *(Backlund, constants $C_B, T_B$)* for every $T \ge T_B$ whose height avoids all zero ordinates, $\bigl|\operatorname{Im}\int_{1/2}^2 \frac{\zeta'}{\zeta}(\sigma+iT)\,d\sigma\bigr| \le C_B \log T$;
--   2. *(vertical side)* $\bigl|\operatorname{Im}\int_{T_1}^{T_2} \frac{\zeta'}{\zeta}(2+it)\,i\,dt\bigr| \le \pi$ for all $T_1, T_2$;
--   3. *(local count, constant $A_0 \ge 1$)* $N(t, t+1) \le A_0 \log(|t|+3)$ for all real $t$;
--   4. *(integral of $\mu$, constants $C_\mu, T_\mu$)* $\bigl|\int_T^{2T}\mu - \frac{T\ell_1(T)}{2\pi}\bigr| \le C_\mu/T$ for $T \ge T_\mu$;
--   5. *($\mu \ll \log$, constant $C_M > 0$)* $|\mu(\tau)| \le C_M\log(\tau+3)$ for $\tau \ge 1$, together with continuity of $\mu$.
--
--   **Conclusion.** For every $T \ge \max(\max(T_B+1,\, T_\mu+1),\, 4)$,
--   $$\Bigl|\,N(T,2T) - \frac{T}{2\pi}\,\ell_1(T)\,\Bigr| \;\le\; \bigl(3|C_B| + 4A_0 + 4C_M + |C_\mu| + 1\bigr)\log T.$$
--
--   Its sole consumer is `Zeta23.RvM.rvM_main_aux`, which instantiates the five parameters from Backlund's bounds, the local count, and the H-$\Gamma$ facts.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/MainTerm.lean#L211-L461

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
open Zeta23
set_option maxHeartbeats 1000000

theorem Zeta23.RvM.rvM_main_param {CB TB A₀ Cμ Tμ CM : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi)
    (hA₀1 : 1 ≤ A₀) (hA₀ : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCμ : ∀ T : ℝ, Tμ ≤ T →
      |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T)
    (hCM0 : 0 < CM) (hCM : ∀ τ : ℝ, 1 ≤ τ → |mu τ| ≤ CM * Real.log (τ + 3))
    (hμc : Continuous mu) :
    ∀ T : ℝ, max (max (TB + 1) (Tμ + 1)) 4 ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T|
        ≤ (3 * |CB| + 4 * A₀ + 4 * CM + |Cμ| + 1) * Real.log T := by sorry
