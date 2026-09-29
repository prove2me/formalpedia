-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_sum_filter_coe
-- name    : Zeta23.ZeroSide.sum_filter_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:44.243416+00:00
-- url     : https://prove2.me/theorems/d553c97d-28d1-4369-98a5-2e52c8f3eb50
-- title:
--   Sum over a subtype filter equals sum over Finset.filter
-- statement:
--   Let $M$ be an additive commutative monoid, $s$ a finite set (`Finset`) of complex numbers, $p$ a predicate on $\mathbb{C}$, and $q$ a predicate on the subtype $\{z \,//\, z \in s\}$ such that $q$ and $p$ agree on elements of $s$: for every $z \in s$, $q(z) \leftrightarrow p(z)$. Let $f : \mathbb{C} \to M$.
--
--   The assertion is a re-indexing identity between two ways of summing $f$ over the elements of $s$ satisfying the predicate:
--   $$\sum_{z \in \{z : s \mid q(z)\}} f(z) \;=\; \sum_{z \in s.\mathrm{filter}\, p} f(z),$$
--   where the left-hand sum runs over the filtered `Finset` of the subtype and the right-hand sum over the filtered `Finset` of $\mathbb{C}$ itself.
--
--   This is bookkeeping for the zero-side block decomposition in `Zeta23.ZeroSide`: the abstract block data indexes zeros by the subtype of the finite zero set $\mathcal{Z}(I')$, while the counting quantities ($s_1$, $s_2$, on-line traces) are phrased via `Finset.filter` on the ambient set of zeros. It is consumed by `Zeta23.ZeroSide.blockInputsAt`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L684-L696

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
omit Z T

theorem Zeta23.ZeroSide.sum_filter_coe {M : Type*} [AddCommMonoid M] (s : Finset ℂ) (p : ℂ → Prop) (q : s → Prop)
    (h : ∀ z : s, q z ↔ p z) (f : ℂ → M) :
    ∑ z ∈ ({z : s | q z} : Finset s), f z = ∑ z ∈ s.filter p, f z := by sorry
