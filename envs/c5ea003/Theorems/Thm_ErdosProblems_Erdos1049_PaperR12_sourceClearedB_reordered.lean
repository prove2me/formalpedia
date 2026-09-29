-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceClearedB_reordered
-- name    : ErdosProblems.Erdos1049.PaperR12.sourceClearedB_reordered
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:06:47.061987+00:00
-- url     : https://prove2.me/theorems/47f8a617-39a4-48e1-897f-69bd063e2c54
-- title:
--   Source cleared b reordered
-- statement:
--   For every n, the cleared B polynomial equals the displayed double sum over the unshifted s,l channels plus the shifted j-channel sum.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBMonomialR12.lean#L161-L174
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

theorem ErdosProblems.Erdos1049.PaperR12.sourceClearedB_reordered (n : ℕ) :
    sourceClearedB n =
      (∑ s ∈ Finset.range (13 * n + 1), ∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      ∑ j ∈ Finset.Icc 1 (14 * n), sourceShiftedASum n j * sourceDQuotient n j := by sorry
