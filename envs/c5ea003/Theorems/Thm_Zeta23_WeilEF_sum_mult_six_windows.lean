-- Prove2me | Theorems.Thm_Zeta23_WeilEF_sum_mult_six_windows
-- name    : Zeta23.WeilEF.sum_mult_six_windows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:49:12.09142+00:00
-- url     : https://prove2.me/theorems/d6eedce1-5c64-4d2c-a90c-79bdffa7ee12
-- title:
--   Total multiplicity in a six-unit window is $\le 6 A_0 \log(|a|+9)$
-- statement:
--   Here `zetaZeroConfig` is the configuration of the nontrivial zeros of $\zeta$ (distinct zeros with their multiplicities), and the hypothesis is a *local count* (`Tail.LocalCount`) for the family of ordinates $\gamma_\rho = \operatorname{Im} \rho$ with multiplicities $m_\rho$: a constant $A_0 \ge 1$ such that every finite set of zeros with ordinates in a unit window $(t, t+1]$ has total multiplicity at most $A_0 \log(|t| + 3)$, for every real $t$.
--
--   **Statement.** For every integer $a$ and every finite set $F$ of zeros whose ordinates lie in $(a, a + 6]$,
--   $$\sum_{\rho \in F} m_\rho \;\le\; 6\, A_0 \log(|a| + 9).$$
--   The window $(a, a+6]$ is covered by six unit windows, and each local bound $A_0 \log(|a + j| + 3)$, $0 \le j \le 5$, is at most $A_0 \log(|a| + 9)$.
--
--   **Role.** In the module `Zeta23.WeilEF.GoodHeights` this bounds the number of zero ordinates near a prospective horizontal height; the pigeonhole argument of `good_heights_at` then finds heights $R \in [j, j+1]$ staying at distance $\gtrsim 1/\log j$ from all ordinates, giving zero-free horizontal contour segments with controlled $\zeta'/\zeta$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/GoodHeights.lean#L99-L144

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_ZetaReflect

open Zeta23
open Complex Set Filter Finset

theorem Zeta23.WeilEF.sum_mult_six_windows {A₀ : ℝ}
    (hLC : Tail.LocalCount (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
      (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.mult ρ) A₀)
    {a : ℤ} (F : Finset zetaZeroConfig.carrier)
    (hF : ∀ ρ ∈ F, (a : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + 6) :
    ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) ≤ 6 * (A₀ * Real.log (|(a : ℝ)| + 9)) := by sorry
