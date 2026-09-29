-- Prove2me | Theorems.Thm_Zeta23_Tail_eventually_tailPackage
-- name    : Zeta23.Tail.eventually_tailPackage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:47:04.104495+00:00
-- url     : https://prove2.me/theorems/0f75e654-e1d2-4222-9b8a-d8b51cc6e23f
-- title:
--   The [prop:tail] package: tail inputs hold eventually with $\theta_0 \le C\,\ell\, T^{\lambda/2-1}$
-- statement:
--   **Setup.** Let $Z$ be an abstract zero configuration satisfying the paper's inputs `PaperInputs Z` (Riemann–von Mangoldt counts, local zero count, the explicit-formula identity, symmetries), and let $P$ be valid parameters with exponent $\lambda \in (0,1]$; write $\ell(T) = \log(T/2\pi)$ and $L = \lambda\ell(T)$. The predicate `Assembly.TailInputs Z P T θ₀` asserts: $\theta_0 \ge 0$; $\tilde E = E/L$ is Hermitian with all eigenvalues at most $\theta_0$ in absolute value ("$\|\tilde E\| \le \theta_0$"); and there is $B \ge 0$ bounding $|\mathrm{tr}\,\hat E|$ and $\|\hat E\|_F$ with $B \le \theta_0/(aL)$ ("$\|\hat E\|_1 \le \theta_0/(aL)$"), where $E = G - A$ is the tail matrix and $\hat E = E/(aL^2)$.
--
--   **Statement.** There exists a function $\theta_0 : \mathbb{R}\to\mathbb{R}$ (concretely $\theta_0(T) = 4A_0C_1^2X^{1/2}\log(4T)/D_0^2 = \theta_0(A_0,\, e^{L/4}C_1,\, T)$) such that:
--   $$\text{(a)}\quad \forall^{\!f} T\to\infty,\ \ \text{TailInputs } Z\ P\ T\ \theta_0(T), \qquad\qquad \text{(b)}\quad \exists C,\ \forall^{\!f} T\to\infty,\ \ \theta_0(T) \le C\,\ell(T)\,T^{\lambda/2 - 1}.$$
--   Part (b) is the paper's "so that" clause "$\theta_0 \le 32A_0\|\varrho''\|_1^2\, l\, T^{\lambda/2-1}$"; since $\lambda \le 1$, this makes $\theta_0(T)$ decay like a power of $T$ (up to the log factor).
--
--   **Role.** This is the final consumer-facing form of Proposition [prop:tail], exported by `Zeta23.Tail.Package` for `Main.lean`: it is consumed directly by `Zeta23.thmA_lam_of_traces`, the trace-level statement from which Theorem A (the $2/3$ critical-line proportion) is derived.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/Package.lean#L31-L50, docstring tag [prop:tail]

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann

open Filter Complex
open Zeta23

theorem Zeta23.Tail.eventually_tailPackage (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by sorry
