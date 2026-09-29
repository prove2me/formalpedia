-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_WeightedRecords_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR8_WeightedRecords_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:47:02.777851+00:00
-- url     : https://prove2.me/theorems/9c8b54cb-bfb9-4284-917e-c8ce1d7fd200
-- title:
--   LCM orbit, strict records, and weighted excess
-- statement:
--   Defines an LCM orbit with positive naturals a,L,U and integer V, satisfying L_(n+1)=lcm(L_n,a_n), gcd(L_n,a_n)U_(n+1)=U_n−V_n, and V_n=L_n−(a_n−1)U_n. A strict record at n means U_(n+1)>U_j for every j≤n. Its raw record charge is max(−V_n−B,0)f(U_n) at strict records and zero otherwise; it also defines bounded/unbounded height and a shifted orbit. Summability equivalences require separate arithmetic and analytic theorems.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR8/WeightedRecords.lean#L1-L409
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR8_WeightedRecords_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR8.WeightedRecords.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordDivergence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_WeightAnalysis_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
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
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Global arithmetic weighted-record theorem

Round 8: complete candidate for long-record `res:arithmeticrecord`.
The finite crossing and CRT lemmas are reused. The proof below supplies the
old large coprime moduli from the *actual record indices*. No supply, global
budget, rate, or normalised-vanishing premise is added.

The natural-weight theorem uses nonsummability. The final theorem derives
that premise from the paper's improper integral through `WeightAnalysis`.
All declarations in this file are compiled candidates.

Pinned Mathlib references used below:
* Data/Nat/GCD/Basic.lean: Nat.Coprime.of_dvd_left, Nat.lcm_dvd.
  Nat.dvd_lcm_left/right and Nat.dvd_gcd are imported Nat/Batteries facts.
* Algebra/Order/BigOperators/Group/Finset.lean: Finset.single_le_sum.
* Topology/Algebra/InfiniteSum/Group.lean: Summable.comp_injective,
  Summable.congr.
Other substantial calls are to the supplied, repaired corpus, not guessed APIs.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter Classical
open scoped BigOperators

/-- Bundles exactly the integer arithmetic in the displayed theorem.
The centring bound is separate so its eventual version can be used later. -/
structure LcmOrbit where
  a : ℕ → ℕ
  L : ℕ → ℕ
  U : ℕ → ℕ
  V : ℕ → ℤ
  apos : ∀ n, 0 < a n
  Lpos : ∀ n, 0 < L n
  Upos : ∀ n, 0 < U n
  nextL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n)
  step : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n
  digit : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * (U n : ℤ)

def Record (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j ≤ n, U j < U (n + 1)

noncomputable def rawRecordWeight (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if Record U n then (((-V n - B).toNat : ℕ) : ℝ) * f (U n) else 0

def HeightBounded (U : ℕ → ℕ) : Prop := ∃ H : ℕ, ∀ n, U n ≤ H

def HeightUnbounded (U : ℕ → ℕ) : Prop := ∀ H : ℕ, ∃ n, H < U n





namespace LcmOrbit













/-- Shift keeps the exact data, not merely their inequalities. -/
def shift (o : LcmOrbit) (T : ℕ) : LcmOrbit where
  a n := o.a (T + n)
  L n := o.L (T + n)
  U n := o.U (T + n)
  V n := o.V (T + n)
  apos n := o.apos (T + n)
  Lpos n := o.Lpos (T + n)
  Upos n := o.Upos (T + n)
  nextL n := by simpa only [Nat.add_assoc] using o.nextL (T + n)
  step n := by simpa only [Nat.add_assoc] using o.step (T + n)
  digit n := o.digit (T + n)

end LcmOrbit

















end ErdosProblems.Erdos243.PaperCompleteR8


