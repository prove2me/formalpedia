-- Prove2me | Theorems.Thm_Zeta23_RvM_reZeroSet_card_le_of_growth
-- name    : Zeta23.RvM.reZeroSet_card_le_of_growth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:24.890017+00:00
-- url     : https://prove2.me/theorems/9ff4dd74-b396-4f2c-9d40-18d71b2d5d35
-- title:
--   Jensen count for $\mathrm{Re}\,\zeta$: $\#\{\sigma \in [\frac12,2] : \mathrm{Re}\,\zeta(\sigma+iT) = 0\} = O(\log T)$
-- statement:
--   **Setup.** For $T \in \mathbb{R}$ let $\mathrm{reZeroSet}(T) = \{\sigma \in [1/2, 2] : \mathrm{Re}\,\zeta(\sigma + iT) = 0\}$.
--
--   **Statement.** Let $A, C$ be real with $C > 0$, and assume the growth bound: for every complex $s$ with $\mathrm{Re}\,s \ge 0.15$ and $\|s - 1\| \ge 1$, $\|\zeta(s)\| \le C\,(|\mathrm{Im}\,s| + 3)^A$. Then for every $T \ge 4$ the set $\mathrm{reZeroSet}(T)$ is finite, and its cardinality satisfies
--
--   $$\#\,\mathrm{reZeroSet}(T) \;\le\; \frac{1}{\log(0.9/0.8)}\,\bigl(|\log(6C)| + 2\max(A, 0)\bigr)\,\log T,$$
--
--   with the constant fully explicit in the growth data $(A, C)$. This is the Jensen half (J) of Backlund's method: the zeros of $\mathrm{Re}\,\zeta(\sigma + iT)$ on $[1/2, 2]$ are among those of the analytic function $f(z) = \tfrac12\bigl(\zeta(z + iT) + \overline{\zeta(\bar z + iT)}\bigr)$ on a disc, where $f$ inherits the polynomial growth of $\zeta$ and $|f|$ is bounded below at the disc center near $\mathrm{Re}\,s = 2$; Jensen's inequality then counts its zeros by $\log T$.
--
--   **Role.** The counting input of the Backlund argument in `Zeta23.RvM.ReZeroCount`: combined with `Zeta23.RvM.backlund_horizontal_of_count` it bounds the horizontal argument variation of $\zeta$, and it is consumed directly by the main Riemann–von Mangoldt theorem `Zeta23.RvM.rvM_main`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ReZeroCount.lean#L98-L348

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
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex Set Metric
open Zeta23
open Zeta23.RvM
set_option maxHeartbeats 1600000

theorem Zeta23.RvM.reZeroSet_card_le_of_growth {A C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A) :
    ∀ T : ℝ, 4 ≤ T → (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ)
      ≤ (1 / Real.log ((0.9 : ℝ) / 0.8) * (|Real.log (6 * C)| + 2 * max A 0)) * Real.log T := by sorry
