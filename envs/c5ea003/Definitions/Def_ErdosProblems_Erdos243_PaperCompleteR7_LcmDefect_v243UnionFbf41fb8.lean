-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:47:34.725303+00:00
-- url     : https://prove2.me/theorems/9ba60638-255a-43d6-9db9-91744232f150
-- title:
--   LCM defect
-- statement:
--   Put A_n=lcm(a_0,...,a_(n-1)) with A_0=1. Defines the real defect (A_n/a_n)(a_n^2/a_(n+1)-1). The initial LCM here is 1, whereas the separate cleared LCM state starts at q. The included identity identifies the product scale starting at q with the canonical denominator; eventual boundedness of this defect is a hypothesis of the endpoint theorem.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR7/LcmDefect.lean#L1-L165
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR7.LcmDefect.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Original-coordinate LCM-prefactor corollary

Compiled end-to-end candidate for short-note `res:lcmbounded`.
The rational denominator q is NOT assumed to divide the prefix LCM.
The proof constructs the lifted integer state, derives its small-error
hypothesis, supplies its one-sided bound from the printed LCM-weighted
expression, and invokes the global CRT argument, not a supply hypothesis.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

noncomputable def lcmDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

theorem productScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  induction n with
  | zero => simp [digitProductScale, canonicalDenominator, prefixProduct]
  | succ n ih =>
      simp only [digitProductScale, ih, canonicalDenominator, prefixProduct_succ]
      ring





end ErdosProblems.Erdos243.PaperCompleteR7


