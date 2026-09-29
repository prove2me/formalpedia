-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_gaussian_first_root_block_zero
-- name    : ErdosProblems.Erdos1049.PaperR13.gaussian_first_root_block_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:11:00.502358+00:00
-- url     : https://prove2.me/theorems/8659cadc-f193-4268-a502-760563e5b215
-- title:
--   Gaussian first root block zero
-- statement:
--   At a primitive ell-th root, the project's Gaussian binomial at (ell,k) is zero for every 0<k<ell.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QLucasR13.lean#L53-L63
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
variable {K : Type*} [Field K]

open ErdosProblems.Erdos1049.PaperR13

theorem ErdosProblems.Erdos1049.PaperR13.gaussian_first_root_block_zero (q : K) {ell k : ℕ}
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hk0 : 0 < k) (hk : k < ell) : gaussBinom q ell k = 0 := by sorry
