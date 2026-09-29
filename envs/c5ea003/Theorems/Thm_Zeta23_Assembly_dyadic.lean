-- Prove2me | Theorems.Thm_Zeta23_Assembly_dyadic
-- name    : Zeta23.Assembly.dyadic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:18.545908+00:00
-- url     : https://prove2.me/theorems/01172c56-7ef9-4d71-9509-c35eab609cf6
-- title:
--   Dyadic summation: from windows $(t, 2t]$ to the cumulative interval $(0, T]$
-- statement:
--   An abstract form of the dyadic-summation step (E4) at the end of the paper's §6 proof of Theorem A. Let $f, g : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be two nonnegative interval functions that are additive over adjacent intervals, i.e. $f(a,c) = f(a,b) + f(b,c)$ whenever $a \le b \le c$ (and likewise for $g$), and suppose $g(0,T) \to \infty$ as $T \to \infty$. Fix a constant $c$.
--
--   Assume the dyadic-window estimate: for every $\varepsilon > 0$ there is $T_1$ such that
--   $$(c - \varepsilon)\, g(t, 2t) \;\le\; f(t, 2t) \quad \text{for all } t \ge T_1.$$
--   Then the cumulative estimate follows: for every $\varepsilon > 0$ there is $T_0$ such that
--   $$(c - \varepsilon)\, g(0, T) \;\le\; f(0, T) \quad \text{for all } T \ge T_0.$$
--
--   In the application, $f = N_0^*$ (distinct on-line zeros) and $g = N$ (all zeros with multiplicity): given $\varepsilon$, one sums the window bound over the dyadic intervals $(T2^{-j}, T2^{-j+1}]$, $j = 1, \dots, J$ with $J$ maximal such that $T2^{-J} \ge T_1$, and absorbs the bounded remainder $N(T2^{-J})$ into $\varepsilon\, g(0,T)$ using $g(0,T) \to \infty$. Consumed by `Zeta23.cumulative_of_dyadic`, which turns the dyadic form of Theorem A into its cumulative form.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L587-L671, docstring: the paper §6, end of the proof of Thm A

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Asymptotics Topology

theorem Zeta23.Assembly.dyadic {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hf_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → f a c = f a b + f b c)
    (hg_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → g a c = g a b + g b c)
    (hf_nn : ∀ a b, 0 ≤ f a b) (hg_nn : ∀ a b, 0 ≤ g a b)
    (hg_top : Tendsto (fun T => g 0 T) atTop atTop)
    (h : ∀ ε > 0, ∃ T₁, ∀ t ≥ T₁, (c - ε) * g t (2 * t) ≤ f t (2 * t)) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * g 0 T ≤ f 0 T := by sorry
