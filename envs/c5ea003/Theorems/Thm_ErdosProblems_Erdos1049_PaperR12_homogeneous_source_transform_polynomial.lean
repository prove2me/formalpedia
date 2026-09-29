-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_transform_polynomial
-- name    : ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform_polynomial
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:57:31.243558+00:00
-- url     : https://prove2.me/theorems/e724f00a-1f60-4d9e-8313-441b373cd0ac
-- title:
--   Homogeneous source transform polynomial
-- statement:
--   For natural u,d and positive natural a,v, the homogeneous source transform specializes to an identity in ℤ[X] at q=X,y=Xᵘ: multiplying the source inner sum by (X;X)_(a−1) equals the displayed finite Gaussian-binomial and homogeneous-Pochhammer sum.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHomogeneousR12.lean#L109-L131
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

theorem ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform_polynomial (u : ℕ) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer (X : ℤ[X]) X (a - 1) *
        homogeneousSourceInner X (X ^ u) a d v =
      ∑ h ∈ Finset.range a, (-1 : ℤ[X]) ^ h * X ^ (h * (d + 1) + h.choose 2) *
        gaussBinom X (a - 1) h * homogeneousPochhammer X (X ^ u) h (v - 1) := by sorry
