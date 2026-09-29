-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_posIndex_smul_pos
-- name    : Zeta23.ZeroSide.posIndex_smul_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:13.432587+00:00
-- url     : https://prove2.me/theorems/50ac849d-928f-4541-87ea-6fbd59d4d409
-- title:
--   Positive index is invariant under positive scaling: $n_+(rA) = n_+(A)$
-- statement:
--   Let $A$ be a Hermitian $n \times n$ matrix over an `RCLike` scalar field $\mathbb{K}$ (i.e. $\mathbb{R}$ or $\mathbb{C}$), and let $r > 0$ be a real number. Here `posIndex` denotes the positive index of inertia $n_+(A)$: the number of positive eigenvalues of a Hermitian matrix, counted with multiplicity (each `posIndex` is taken with respect to a supplied proof of Hermitianity, so the statement carries both the witness for $A$ and one for $rA$).
--
--   The assertion is that scaling by a positive real scalar does not change the positive index:
--   $$n_+\big((r : \mathbb{K}) \cdot A\big) = n_+(A).$$
--
--   This is a small piece of the Sylvester-inertia toolkit of the zero-side (§4) argument. The project works with the same matrix in two normalizations — tilde units $\tilde{A} = A/L$ and hat units $\hat{A} = A/(aL^2)$ — and this lemma lets positive-index bounds transfer between them. It is consumed by `Zeta23.ZeroSide.ZeroBlockData.posIndex_blockQ_le` and by `Zeta23.ZeroSide.blockInputsAt` in the module `Zeta23.ZeroSide`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L112-L126

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
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Zeta23.ZeroSide.posIndex_smul_pos {A : Matrix n n 𝕜} (hA : A.IsHermitian) {r : ℝ} (hr : 0 < r)
    (hrA : ((r : 𝕜) • A).IsHermitian) : posIndex hrA = posIndex hA := by sorry
