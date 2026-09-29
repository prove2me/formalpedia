-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_middle_channel_initial
-- name    : ErdosProblems.Erdos1049.PaperR12.actual_middle_channel_initial
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:14:21.685974+00:00
-- url     : https://prove2.me/theorems/506d35c3-80fa-487c-8f0c-627bccb4d4d6
-- title:
--   Actual middle channel initial
-- statement:
--   For every natural n≥1, the coefficient at degree M(n) of sourceShiftedASum(n,n)·sourceDQuotient(n,n) is 1.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBInitialR12.lean#L86-L108
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
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/
open Polynomial PaperR11
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR12

open ErdosProblems.Erdos1049.PaperR11

theorem ErdosProblems.Erdos1049.PaperR12.actual_middle_channel_initial (n : ℕ) (hn : 1 ≤ n) :
    (sourceShiftedASum n n * sourceDQuotient n n).coeff (sourceM n) = 1 := by sorry
