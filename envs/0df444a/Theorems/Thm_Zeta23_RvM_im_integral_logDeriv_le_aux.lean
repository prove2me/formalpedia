-- Prove2me | Theorems.Thm_Zeta23_RvM_im_integral_logDeriv_le_aux
-- name    : Zeta23.RvM.im_integral_logDeriv_le_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:11.611636+00:00
-- url     : https://prove2.me/theorems/db9995f7-cd5f-46f4-a633-b5626a7bb22c
-- title:
--   Backlund induction: $\bigl|\mathrm{Im}\int_u^v \zeta'/\zeta\bigr| \le 2\pi\,(\#(P \cap (u,v)) + 1)$
-- statement:
--   **Statement.** Let $T \ne 0$ be a real number with $\zeta(\sigma + iT) \ne 0$ for all $\sigma \in [1/2, 2]$, and let $P$ be a finite set of reals containing every $\sigma \in [1/2, 2]$ with $\mathrm{Re}\,\zeta(\sigma + iT) = 0$. Then for every natural number $n$ and all $u, v$ with $1/2 \le u < v \le 2$ such that $\#\bigl(P \cap (u, v)\bigr) \le n$,
--
--   $$\Bigl|\,\mathrm{Im} \int_{u}^{v} \frac{\zeta'}{\zeta}(\sigma + iT)\, d\sigma\,\Bigr| \;\le\; 2\pi\,\Bigl(\#\bigl(P \cap (u, v)\bigr) + 1\Bigr),$$
--
--   where $\#(P \cap (u,v))$ is the cardinality of the set of points of $P$ strictly between $u$ and $v$. (The auxiliary bound $n$ is the variable of the strong induction: splitting $(u,v)$ at a point of $P$ strictly decreases the count on each side, and the zero-free base case contributes $2\pi$ per piece via `Zeta23.RvM.im_integral_le_two_pi`.)
--
--   **Role.** The inductive engine of Backlund's bound in `Zeta23.RvM.Backlund`: instantiated with $P$ = the zeros of $\mathrm{Re}\,\zeta(\cdot + iT)$ on $[1/2, 2]$ and $(u,v) = (1/2, 2)$, it yields the parametric horizontal bound `Zeta23.RvM.backlund_horizontal_of_count_at` and thence the $O(\log T)$ argument bound of the Riemann–von Mangoldt formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Backlund.lean#L184-L262

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

open Complex Set MeasureTheory Real intervalIntegral
attribute [-instance] LieAlgebra.ofAssociativeAlgebra
variable {T : ℝ}

theorem Zeta23.RvM.im_integral_logDeriv_le_aux (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (P : Finset ℝ) (hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P) :
    ∀ n : ℕ, ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card ≤ n →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ 2 * Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by sorry
