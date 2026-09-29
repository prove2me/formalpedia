-- Prove2me | Theorems.Thm_Zeta23_Tail_LocalCount_ofWindowCount
-- name    : Zeta23.Tail.LocalCount.ofWindowCount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:06.453466+00:00
-- url     : https://prove2.me/theorems/9b19f791-a1bb-4470-8e36-273f21e51add
-- title:
--   From the window count on $N$ to the finite-sub-family `LocalCount`
-- statement:
--   Let $Z$ be a `ZeroConfig`: an abstract configuration of distinct points $\rho = \beta + i\gamma$ in the closed strip $0 \le \beta \le 1$ with multiplicities $m_\rho \ge 1$ (`Z.mult`), locally finite in the ordinate and invariant under $\rho \mapsto 1 - \bar\rho$. Its counting function $Z.N(T_1, T_2)$ sums multiplicities over the window $T_1 < \gamma \le T_2$.
--
--   The predicate `LocalCount γ m A₀` (from `Zeta23/Tail/Basic.lean`) asserts, for an abstract family of ordinates $\gamma : \iota \to \mathbb{R}$ with multiplicities $m : \iota \to \mathbb{N}$: (i) $A_0 \ge 1$, and (ii) for every real $t$ and every **finite** sub-family $s$ whose ordinates all lie in $(t, t+1]$, $\sum_{\rho \in s} m_\rho \le A_0 \log(|t|+3)$ — a formulation that presupposes no summability.
--
--   **Statement.** If $A_0 \ge 1$ and the two-sided unit-window bound $Z.N(t, t+1) \le A_0\log(|t|+3)$ holds for all real $t$, then `LocalCount` holds for the family of all distinct zeros $\rho \in Z.\mathrm{carrier}$ (as a subtype), with ordinate $\gamma_\rho = \operatorname{Im}\rho$ and multiplicity $m_\rho = Z.\mathrm{mult}\,\rho$.
--
--   This is the bridge from the paper input H-RvM's local count to the form used by the tail estimates: it feeds `Zeta23.Tail.NII_le`, `Zeta23.Tail.TailHyp.partial_sum_le`, and the convergence lemmas `Zeta23.WeilEF.good_heights_at` and `Zeta23.WeilEF.zero_sum_inv_sq_gen`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L116-L137

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

theorem Zeta23.Tail.LocalCount.ofWindowCount (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ := by sorry
