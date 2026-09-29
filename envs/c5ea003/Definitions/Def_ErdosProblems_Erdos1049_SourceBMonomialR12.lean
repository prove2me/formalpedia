-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
-- name    : ErdosProblems_Erdos1049_SourceBMonomialR12
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:49:50.69197+00:00
-- url     : https://prove2.me/theorems/c1046876-a1b3-461a-ba93-aa4755615600
-- title:
--   The actual B monomial cancellation
-- statement:
--   A homogeneous finite identity inside ℤ[X] removes X^M from the already cleared B numerator, including the late shifted channels. The submitted module contains the source declarations sourceShiftedASum, X_power_dvd_signed_summand, sourceShiftedASummand_early_dvd, sourceHomogeneousBase, sourceHomogeneousOrder, among others. Source topic: The actual B monomial cancellation.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBMonomialR12.lean#L20-L209
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

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
# The actual B monomial cancellation



The late j-channel is treated by a homogeneous finite identity in Z[X].
No endpoint divisibility, Laurent membership, source package, or initial-order
assertion is assumed. This removes X^M from the actual integral numerator D*B.
The additional cyclotomic Omega cancellation is a different theorem and is
not asserted in this file.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators

noncomputable def sourceShiftedASum (n j : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceShiftedASummand n s j





/-- The exponent used to homogenise all the negative-shift channels. -/
def sourceHomogeneousBase (n j u : ℕ) : ℕ :=
  sourceM n + 2 * n ^ 2 - (2 * n * j + 13 * n * u)

def sourceHomogeneousOrder (n u : ℕ) : ℕ :=
  13 * n * u + (u + 1) * (2 * n + 1) + (u + 1).choose 2

















/-- Canonical polynomial quotient, not an unspecified chosen witness. -/
noncomputable def sourceBWithoutMonomial (n : ℕ) : ℤ[X] :=
  sourceClearedB n /ₘ ((X : ℤ[X]) ^ sourceM n)





end ErdosProblems.Erdos1049.PaperR12


