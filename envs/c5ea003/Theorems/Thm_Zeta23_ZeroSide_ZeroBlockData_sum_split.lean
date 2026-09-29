-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_sum_split
-- name    : Zeta23.ZeroSide.ZeroBlockData.sum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:45.515581+00:00
-- url     : https://prove2.me/theorems/19fb8208-ee2f-4ed5-858d-bd2ed5a3d4d5
-- title:
--   Splitting a sum over $\mathcal{Z}(I')$ into on-line points and off-line pairs
-- statement:
--   Let $D$ be abstract zero-side data (`ZeroBlockData` on a finite index type $\iota$, with involution $\sigma$ modelling $\rho \mapsto 1 - \bar\rho$), and let $P$ be a choice of pair representatives (`PairReps`): a finite set $R \subseteq \iota$ containing exactly one member of each off-line pair — formally, $\sigma z \ne z$ and $\sigma z \notin R$ for $z \in R$, and every $z$ with $\sigma z \ne z$ has $z \in R$ or $\sigma z \in R$.
--
--   **Statement.** For every function $f : \iota \to M$ into an additive commutative monoid,
--   $$\sum_{z} f(z) \;=\; \sum_{z \text{ on-line}} f(z) \;+\; \sum_{z \in R} \bigl( f(z) + f(\sigma z) \bigr),$$
--   i.e. the full sum over $\mathcal{Z}(I') = \mathcal{S}_1 \cup \mathcal{S}_2 \cup \bigcup \mathcal{P}$ splits into the on-line points (those fixed by $\sigma$) and the off-line pairs, each pair contributing both of its members.
--
--   **Role.** This combinatorial identity underlies the whole block decomposition of the module `Zeta23.ZeroSide`: it is used in `posIndex_blockA_le` and `posIndex_blockQ_le` (splitting the matrix $A$ into on-line and pair parts), in `card_offLine_eq_mk` ($\#\mathrm{offLine} = 2p$), and in the packaging theorem `blockInputsAt`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L231-L259

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
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
open ZeroBlockData
variable (D : ZeroBlockData ι d)
variable {D}
variable (D) (P : D.PairReps)

theorem Zeta23.ZeroSide.ZeroBlockData.sum_split {M : Type*} [AddCommMonoid M] (f : ι → M) :
    ∑ z, f z = ∑ z ∈ D.onLine, f z + ∑ z ∈ P.R, (f z + f (D.σ z)) := by sorry
