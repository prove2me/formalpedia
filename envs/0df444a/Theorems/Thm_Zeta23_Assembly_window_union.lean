-- Prove2me | Theorems.Thm_Zeta23_Assembly_window_union
-- name    : Zeta23.Assembly.window_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:35.343024+00:00
-- url     : https://prove2.me/theorems/79c21fe9-e4e3-4bc5-8f77-4c418aab6b75
-- title:
--   Splitting a zero window: $\mathcal{Z}(a,c] = \mathcal{Z}(a,b] \cup \mathcal{Z}(b,c]$
-- statement:
--   For an abstract zero configuration $Z$, the window $\mathcal{Z}(T_1, T_2] := \{\rho \in \mathcal{Z} : T_1 < \operatorname{Im}\rho \le T_2\}$ is the set of distinct zeros with ordinate in the half-open interval $(T_1, T_2]$.
--
--   The theorem asserts that windows split at any intermediate point: for real numbers $a \le b \le c$,
--   $$\mathcal{Z}(a, c] \;=\; \mathcal{Z}(a, b] \,\cup\, \mathcal{Z}(b, c]$$
--   as an equality of sets (and the two pieces are disjoint by the half-open convention).
--
--   This is the set-level fact behind all interval additivity of zero-counting functions in the project: it feeds `N0star_add` (additivity of the distinct on-line count), the seam inequality `seamA`, and the dyadic summation `Zeta23.cumulative_of_dyadic`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L882-L893

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
open Set
variable (Z : ZeroConfig)

theorem Zeta23.Assembly.window_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by sorry
