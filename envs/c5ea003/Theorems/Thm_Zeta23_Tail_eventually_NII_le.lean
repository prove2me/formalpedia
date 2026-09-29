-- Prove2me | Theorems.Thm_Zeta23_Tail_eventually_NII_le
-- name    : Zeta23.Tail.eventually_NII_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:35.731477+00:00
-- url     : https://prove2.me/theorems/c75170e8-1e94-4f0c-b961-05a60c254c46
-- title:
--   Eventual boundary count: $N(I'\setminus I) \le C\sqrt{T}\,\ell(T)$ for large $T$
-- statement:
--   **Setup.** Let $Z$ be an abstract zero configuration, with $Z.N\,a\,b$ counting (with multiplicity) the zeros with ordinate in $(a, b]$. The quantity `Assembly.NII Z T` is the boundary count
--   $$N(I'\setminus I) \;=\; Z.N(T - D_0)\,T \;+\; Z.N(2T)\,(2T + D_0), \qquad D_0 := \sqrt{T},$$
--   the number of zeros in the two strips separating $I = [T,2T]$ from $I' = (T-\sqrt T,\, 2T+\sqrt T]$. Assume $A_0 \ge 1$ and the two-sided unit-window local count: for every real $t$, $Z.N\,t\,(t+1) \le A_0\log(|t|+3)$. Write $\ell(T) = \log(T/2\pi)$.
--
--   **Statement.** There exists a constant $C$ (the proof gives $C = 6A_0$) such that, for all sufficiently large $T$ (Lean's `∀ᶠ T in atTop`),
--   $$N(I'\setminus I) \;\le\; C\,\sqrt{T}\,\ell(T).$$
--
--   **Role.** This is the eventually-in-$T$ form of the paper's "$N(I'\setminus I) \ll D_0\, l$". It is consumed by `Zeta23.eventually_side_conditions`, one of the side conditions assembled in the final derivation of Theorem A: the boundary zeros are few enough ($O(\sqrt T\, \ell)$ versus $N(T,2T) \asymp T\ell$) to be negligible in the zero-counting bookkeeping.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L674-L684

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

theorem Zeta23.Tail.eventually_NII_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ C : ℝ, ∀ᶠ T in atTop, (Assembly.NII Z T : ℝ) ≤ C * Real.sqrt T * l T := by sorry
