-- Prove2me | Theorems.Thm_Zeta23_Assembly_eventually_N_ge
-- name    : Zeta23.Assembly.eventually_N_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:38.59404+00:00
-- url     : https://prove2.me/theorems/a8a50268-ea80-4c4e-89fa-22b08c5e5abd
-- title:
--   Riemann–von Mangoldt lower bound: $N(T,2T) \ge T l/(4\pi)$ eventually
-- statement:
--   Let $Z$ be an abstract zero configuration and $N(T,2T)$ its zero count with multiplicity in the window $T < \gamma \le 2T$. Write $l = l(T) := \log(T/2\pi)$ and $\ell_1 := l + 2\log 2 - 1$. Assume the Riemann–von Mangoldt hypothesis H-RvM for $Z$: $N(T,2T) = \frac{T}{2\pi}\ell_1 + O(\log T)$ ([eq:RvM]) together with the local count $N(t, t+1) \ll \log(|t|+3)$.
--
--   Then, for all sufficiently large $T$,
--   $$\frac{T\, l(T)}{4\pi} \;\le\; N(T, 2T).$$
--
--   Indeed $\ell_1 \ge l$, so the main term alone is $\ge T l/(2\pi)$, and half of it eventually absorbs the $O(\log T)$ error. This crude but convenient lower bound is used in `thmA_abstract_err` (to show the explicit error terms are $o(N)$) and in `Zeta23.cumulative_of_dyadic` (to verify $N(0,T) \to \infty$ for the dyadic summation).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L712-L731, docstring tag [eq:RvM]

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
open Filter Asymptotics Topology Real

theorem Zeta23.Assembly.eventually_N_ge (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    ∀ᶠ T in atTop, T * l T / (4 * π) ≤ (Z.N T (2 * T) : ℝ) := by sorry
