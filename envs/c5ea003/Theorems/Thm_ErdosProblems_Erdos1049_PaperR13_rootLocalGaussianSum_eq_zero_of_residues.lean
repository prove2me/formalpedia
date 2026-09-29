-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_rootLocalGaussianSum_eq_zero_of_residues
-- name    : ErdosProblems.Erdos1049.PaperR13.rootLocalGaussianSum_eq_zero_of_residues
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:47:15.082005+00:00
-- url     : https://prove2.me/theorems/f3cf7720-0ea9-4494-a3c9-08893edd4ce6
-- title:
--   Root local gaussian sum eq zero of residues
-- statement:
--   For a nonzero primitive ell-th root, if v<ell, a+r=v, and ell≤r+v, the local Gaussian sum is zero.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/RootUnityLocalCancellationR13.lean#L152-L158
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

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Finset
open scoped BigOperators
variable {K : Type*} [Field K]

open ErdosProblems.Erdos1049.PaperR13

theorem ErdosProblems.Erdos1049.PaperR13.rootLocalGaussianSum_eq_zero_of_residues (q : K) (hq : q ≠ 0)
    {ell w a r v : ℕ} (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hv : v < ell) (harv : a + r = v) (hrv : ell ≤ r + v) :
    rootLocalGaussianSum q w a r v = 0 := by sorry
