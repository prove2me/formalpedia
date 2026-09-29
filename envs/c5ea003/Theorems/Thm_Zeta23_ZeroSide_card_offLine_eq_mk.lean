-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_card_offLine_eq_mk
-- name    : Zeta23.ZeroSide.card_offLine_eq_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:38.197182+00:00
-- url     : https://prove2.me/theorems/3ff7b4e6-0e29-45b3-b418-5abb03b54d7c
-- title:
--   The off-line zeros of the window come in pairs: $\#\mathrm{offLine} = 2p$
-- statement:
--   For a zero configuration $Z$ and height $T$, the off-line set `Z.offLine T` consists of the zeros of the window $\mathcal{Z}(I')$, $I' = (T - D_0, 2T + D_0]$, with $\operatorname{Re}\rho \ne 1/2$. `mkPairReps` is the canonical choice of representatives of the off-line pairs $\{\rho, 1 - \bar\rho\}$ — the members with $\operatorname{Re}\rho > 1/2$ — for the block data built from any $\sigma$-equivariant family of evaluation vectors $v$ (the statement does not depend on $v$), and $p$ is the number of representatives.
--
--   **Statement.**
--   $$\#\, (Z.\mathrm{offLine}\ T) \;=\; 2\, p$$
--   (`Set.ncard` on the left): the off-line zeros are partitioned into disjoint two-element pairs $\{\rho, 1 - \bar\rho\}$ by the reflection, so their number is exactly twice the number of pairs.
--
--   **Role.** In the module `Zeta23.ZeroSide` this reconciles the paper's count $p = \#\mathcal{P}$ (defined in Lean as $\#\mathrm{offLine}/2$) with the abstract pair-representative count, and feeds the packaging theorem `blockInputsAt` via `p_eq_mk`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L728-L739

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide

set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
open Zeta23 Classical
variable (Z : ZeroConfig) (T : ℝ)
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

theorem Zeta23.ZeroSide.card_offLine_eq_mk : (Z.offLine T).ncard = 2 * (mkPairReps Z T v hv).p := by sorry
