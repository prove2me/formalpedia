-- Prove2me | Theorems.Thm_Zeta23_RvM_rvM_main_aux
-- name    : Zeta23.RvM.rvM_main_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:42:28.603724+00:00
-- url     : https://prove2.me/theorems/d2029f1f-2e80-475d-81ff-190853cbcf29
-- title:
--   Riemann-von Mangoldt assembly from the two Backlund contour bounds
-- statement:
--   This is the assembly step for the Riemann-von Mangoldt formula, stated with its two contour-integral inputs as explicit hypotheses. As elsewhere, $N(T,2T)$ (`zetaZeroConfig.N`) counts nontrivial zeros with imaginary part in $(T, 2T]$ with multiplicity, and $\ell_1(T) = \log\frac{T}{2\pi} + 2\log 2 - 1$.
--
--   **Statement.** Assume:
--   * `GammaFacts` (the H-$\Gamma$ Stirling facts for the density $\mu$);
--   * a *horizontal Backlund bound* in existential form: there exist $C, T_0$ such that for every $T \ge T_0$ at which no nontrivial zero has ordinate exactly $T$, $$\Bigl|\operatorname{Im}\int_{1/2}^{2} \frac{\zeta'}{\zeta}(\sigma + iT)\,d\sigma\Bigr| \le C\log T;$$
--   * the *vertical bound on the 2-line*: for all $T_1, T_2$, $\bigl|\operatorname{Im}\int_{T_1}^{T_2} \frac{\zeta'}{\zeta}(2+it)\,i\,dt\bigr| \le \pi$.
--
--   Then there exist $C, T_0$ such that for all $T \ge T_0$,
--   $$\Bigl|\,N(T,2T) - \frac{T}{2\pi}\,\ell_1(T)\,\Bigr| \;\le\; C\log T.$$
--
--   The proof instantiates the fully parametric version `rvM_main_param` with the existential witnesses of the two hypotheses, the local zero count, H-$\Gamma$'s integral of $\mu$, the bound $\mu \ll \log$, and continuity of $\mu$. Its sole consumer is `Zeta23.RvM.rvM_main`, which discharges the two hypotheses by the theorems `backlund_horizontal` and `vertical_two`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/MainTerm.lean#L463-L477

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

theorem Zeta23.RvM.rvM_main_aux (hΓ : GammaFacts)
    (backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by sorry
