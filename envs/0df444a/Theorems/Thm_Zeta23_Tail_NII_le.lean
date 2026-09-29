-- Prove2me | Theorems.Thm_Zeta23_Tail_NII_le
-- name    : Zeta23.Tail.NII_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:34.220214+00:00
-- url     : https://prove2.me/theorems/fd4a5872-ce61-4f72-a0cb-c02c87e857e8
-- title:
--   Boundary-window count: $N(I'\setminus I) \le 3A_0\sqrt{T}\,\log(4T)$
-- statement:
--   Let $Z$ be a `ZeroConfig` (an abstract locally finite, reflection-invariant multiset of points in the strip with multiplicities), and set $D_0 := \sqrt{T}$. The quantity `Assembly.NII Z T` is the number of zeros (with multiplicity) in the two boundary slivers of the extended window $I' = (T - D_0,\, 2T + D_0]$ around $I = (T, 2T]$:
--   $$N(I' \setminus I) \;=\; Z.N(T - D_0,\, T) \;+\; Z.N(2T,\, 2T + D_0).$$
--
--   **Statement.** Suppose $A_0 \ge 1$ and the two-sided local count $Z.N(t, t+1) \le A_0 \log(|t|+3)$ holds for all real $t$. Then for every $T \ge T_0$ (the absolute threshold $T_0 = 300$ of `Zeta23/Tail/Basic.lean`),
--   $$N(I' \setminus I) \;\le\; 3\,A_0\,\sqrt{T}\,\log(4T).$$
--
--   Since $\log(4T) \le 2\,l$ with $l = \log\frac{T}{2\pi}$ in this range, this realizes the paper's estimate $N(I'\setminus I) \ll D_0\, l$ from [prop:zeroside]: the boundary slivers of width $\sqrt T$ contribute negligibly compared with $N(T,2T) \asymp T\,l$. Its consumer is `Zeta23.Tail.eventually_NII_le`, which feeds the zero-side bookkeeping of the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L589-L636, docstring tag [prop:zeroside]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
open Filter
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem Zeta23.Tail.NII_le (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hT : T₀ ≤ T) :
    (Assembly.NII Z T : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by sorry
