-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_ReciprocalPochhammerR14
-- name    : ErdosProblems_Erdos1049_ReciprocalPochhammerR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:13.77805+00:00
-- url     : https://prove2.me/theorems/76f4813b-1853-4716-b120-1d165c786a64
-- title:
--   Reciprocal factorials and reflected finite products
-- statement:
--   Finite q-factorials are reversed exactly, including the triangular exponent, and reflected numerator products remove reciprocal powers. The submitted module contains the source declarations triangularExponent, triangularExponent_succ, inverse_power_mul_power, reciprocal_factor, qPochhammer_reciprocal, among others. Source topic: Reciprocal factorials and reflected finite products.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/ReciprocalPochhammerR14.lean#L18-L153
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_FiniteResidueInterpolationR14
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Reciprocal factorials and reflected finite products

Reversal of finite q-factorials and the erased pole product. These are finite algebraic
identities. In particular no analytic source identity is used as a premise.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Finset Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def triangularExponent (m : ℕ) : ℕ := m.choose 2 + m





















end ErdosProblems.Erdos1049.PaperR14


