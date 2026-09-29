-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_transform
-- name    : ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:54:02.038573+00:00
-- url     : https://prove2.me/theorems/87571302-ccfe-4814-a593-a8c21b76a6e1
-- title:
--   Homogeneous source transform
-- statement:
--   Over a field, for q and nonzero y, positive natural a,v and natural d, multiplying homogeneousSourceInner(q,y,a,d,v) by (q;q)_(a−1) gives the displayed finite sum over 0≤h<a of (−1)ʰ q^(h(d+1)+choose(h,2)) times the Gaussian binomial (a−1 choose h)_q and homogeneousPochhammer(q,y,h,v−1).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHomogeneousR12.lean#L86-L107
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

theorem ErdosProblems.Erdos1049.PaperR12.homogeneous_source_transform {K : Type*} [Field K]
    (q y : K) (hy : y ≠ 0) {a d v : ℕ} (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * homogeneousSourceInner q y a d v =
      ∑ h ∈ Finset.range a, (-1 : K) ^ h * q ^ (h * (d + 1) + h.choose 2) *
        gaussBinom q (a - 1) h * homogeneousPochhammer q y h (v - 1) := by sorry
