-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
-- name    : ErdosProblems_Erdos1049_SourceRootCarriesR13
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:53:43.188127+00:00
-- url     : https://prove2.me/theorems/d3319fa9-dbfa-410a-bc0e-19b6312e1892
-- title:
--   Exact source carry geometry and the first Omega channel
-- statement:
--   The source weight is rewritten in exact carry coordinates; first- and second-carry root windows are classified before global block cancellation. The submitted module contains the source declarations sourceCarryOne, sourceCarryTwo, floor_nat_ratio_int, sourceWeight_eq_carries, sourceWeight_one_carry_cases, among others. Source topic: Exact source carry geometry and the first Omega channel.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceRootCarriesR13.lean#L18-L217
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
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
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
# Exact source carry geometry and the first Omega channel


The carry expressions are linked to the literal sourceWeight. The first
carry case is carried through to the actual cleared B polynomial. The
second case supplies its exact local-window geometry and constant harmonic
floor; its global residue-block assembly is not asserted by this file.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators

def sourceCarryOne (n ell : ℕ) : ℤ :=
  ((14 * n / ell : ℕ) : ℤ) + (13 * n / ell : ℕ) - (12 * n / ell : ℕ) - (15 * n / ell : ℕ)

def sourceCarryTwo (n ell : ℕ) : ℤ :=
  2 * ((14 * n / ell : ℕ) : ℤ) - (13 * n / ell : ℕ) - (15 * n / ell : ℕ)



















section Field
variable {K : Type*} [Field K]











end Field
end ErdosProblems.Erdos1049.PaperR13


