-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_covering_of_crt_block
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.covering_of_crt_block
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:48:12.533308+00:00
-- url     : https://prove2.me/theorems/abf87258-ace2-41b2-acf1-a6b234c82200
-- title:
--   One CRT block covers all its translated walls
-- statement:
--   Take B moduli m_i>B, each dividing a period P and an integer L, and suppose m_i divides x+i for every i<B. For any k, each integer immediately below the wall x+B+kP, in its length-B predecessor interval, has a divisor d>B that also divides L.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L21-L48
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

namespace LcmRecordExcess
end LcmRecordExcess

/-!
# Counting the CRT heights crossed by one arithmetic step

The heights are the actual arithmetic progression `x + k * P`, not an
assumed cardinality bound. This supplies the finite local charging step in
the weighted-record argument of `LcmRecordExcess.md`. First-crossing existence,
uniqueness, and the finite partition across time require no monotonicity of
the numerator sequence. The existing CRT construction supplies the covering
from any finite family of sufficiently large pairwise-coprime old divisors.
Producing that family from an infinite canonical orbit and the analytic
divergence argument are not asserted by this module.
-/


open LcmRecordExcess

open ErdosProblems.Erdos243.LcmRecordCrossing

open ErdosProblems.Erdos243.LcmRecordExcess

theorem ErdosProblems.Erdos243.LcmRecordCrossing.covering_of_crt_block {B : ℕ} (m : Fin B → ℕ)
    (x P k : ℕ) (L : ℤ)
    (hm : ∀ i, B < m i) (hmP : ∀ i, m i ∣ P)
    (hmL : ∀ i, (m i : ℤ) ∣ L)
    (hresidue : ∀ i, m i ∣ x + i.1) :
    ∀ z : ℤ, (x + B + k * P : ℕ) - (B : ℤ) ≤ z →
      z < (x + B + k * P : ℕ) →
      ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by sorry
