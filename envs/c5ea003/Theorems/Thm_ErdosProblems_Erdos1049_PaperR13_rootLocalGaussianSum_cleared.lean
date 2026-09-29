-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_rootLocalGaussianSum_cleared
-- name    : ErdosProblems.Erdos1049.PaperR13.rootLocalGaussianSum_cleared
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:42:26.654216+00:00
-- url     : https://prove2.me/theorems/0ef97d6d-0541-44df-8646-58796cebecff
-- title:
--   Root local gaussian sum cleared
-- statement:
--   For nonzero q, multiplication of the local Gaussian sum by (q;q)_a yields the explicit finite q-binomial/Pochhammer sum with its integer shift exponent.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/RootUnityLocalCancellationR13.lean#L114-L131
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

theorem ErdosProblems.Erdos1049.PaperR13.rootLocalGaussianSum_cleared (q : K) (hq : q ≠ 0) (w a r v : ℕ) :
    rootLocalGaussianSum q w a r v * qPochhammer q q a =
      ∑ j ∈ range (a + 1),
        qBinomialTerm q (q ^ ((w : ℤ) - a + 1)) a j *
          qPochhammer q (q ^ (r + 1) * q ^ j) v := by sorry
