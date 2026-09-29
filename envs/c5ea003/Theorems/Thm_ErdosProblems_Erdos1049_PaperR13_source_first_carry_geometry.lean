-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_source_first_carry_geometry
-- name    : ErdosProblems.Erdos1049.PaperR13.source_first_carry_geometry
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:18:51.959086+00:00
-- url     : https://prove2.me/theorems/d54a6f5c-a2cd-4def-a3c4-3ffae1077219
-- title:
--   Source first carry geometry
-- statement:
--   For positive ell and first carry one, the three displayed residue equalities and inequalities identify the wrapped first-carry root window.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceRootCarriesR13.lean#L63-L81
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
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
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

namespace PaperR12
end PaperR12

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR13

open ErdosProblems.Erdos1049.PaperR11
open ErdosProblems.Erdos1049.PaperR12

theorem ErdosProblems.Erdos1049.PaperR13.source_first_carry_geometry (n ell : ℕ) (hell : 0 < ell)
    (hcarry : sourceCarryOne n ell = 1) :
    ell ≤ (12 * n) % ell + (2 * n) % ell ∧
    (13 * n) % ell + (2 * n) % ell < ell ∧
    (14 * n) % ell + ell = (12 * n) % ell + (2 * n) % ell := by sorry
