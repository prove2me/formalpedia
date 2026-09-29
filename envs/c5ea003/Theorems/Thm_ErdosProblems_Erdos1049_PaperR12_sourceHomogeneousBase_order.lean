-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceHomogeneousBase_order
-- name    : ErdosProblems.Erdos1049.PaperR12.sourceHomogeneousBase_order
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:01:26.604709+00:00
-- url     : https://prove2.me/theorems/fb2651b4-c1d8-41d2-a7f2-f7195c82b281
-- title:
--   Source homogeneous base order
-- statement:
--   When j=n+u+1 within the displayed bounds, the homogeneous base plus its order equals M(n)+(u+1)+binomial(u+1,2).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBMonomialR12.lean#L135-L142
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
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
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

namespace PaperR11
end PaperR11

/-!
# The actual B monomial cancellation



The late j-channel is treated by a homogeneous finite identity in Z[X].
No endpoint divisibility, Laurent membership, source package, or initial-order
assertion is assumed. This removes X^M from the actual integral numerator D*B.
The additional cyclotomic Omega cancellation is a different theorem and is
not asserted in this file.
-/
open Polynomial
open PaperR11
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR12

open ErdosProblems.Erdos1049.PaperR11

theorem ErdosProblems.Erdos1049.PaperR12.sourceHomogeneousBase_order (n j u : ℕ) (hj : j ≤ 14 * n)
    (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceHomogeneousBase n j u + sourceHomogeneousOrder n u =
      sourceM n + (u + 1) + (u + 1).choose 2 := by sorry
