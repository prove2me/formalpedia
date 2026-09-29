-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneousPochhammer_zero
-- name    : ErdosProblems.Erdos1049.PaperR12.homogeneousPochhammer_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:46:24.170579+00:00
-- url     : https://prove2.me/theorems/3d9784db-fb63-4049-befc-ba34ddb6f8e1
-- title:
--   Homogeneous pochhammer zero
-- statement:
--   For natural u,h,N with h≤u<N, the homogeneous Pochhammer expression at (X,Xᵘ,h,N) is zero.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHomogeneousR12.lean#L169-L175
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Homogeneous finite transform and monomial cancellation tools

Homogenisation removes the need to assert
that a Laurent expression is an integral polynomial. The identity is first
proved in a field, then pulled back through the injective fraction-field map.
The final displayed identity is entirely in Z[X].
-/
open Polynomial
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR12

theorem ErdosProblems.Erdos1049.PaperR12.homogeneousPochhammer_zero (u h N : ℕ) (hu : u < N) (hh : h ≤ u) :
    homogeneousPochhammer (X : ℤ[X]) (X ^ u) h N = 0 := by sorry
