-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_quotient_remainder_successor_no_carry
-- name    : ErdosProblems.Erdos1049.PaperR13.quotient_remainder_successor_no_carry
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:14:08.111388+00:00
-- url     : https://prove2.me/theorems/93dd0206-4bcd-40e8-85ce-ef55483e9eec
-- title:
--   Quotient remainder successor no carry
-- statement:
--   When (n mod ell)+1<ell and ell>0, incrementing n preserves the quotient and increments the remainder.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QLucasR13.lean#L14-L21
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


open ErdosProblems.Erdos1049.PaperR13

theorem ErdosProblems.Erdos1049.PaperR13.quotient_remainder_successor_no_carry {ell n : ℕ} (hell : 0 < ell)
    (h : n % ell + 1 < ell) :
    (n + 1) / ell = n / ell ∧ (n + 1) % ell = n % ell + 1 := by sorry
