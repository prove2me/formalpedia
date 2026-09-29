-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_exists_crt_covering_progression
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.exists_crt_covering_progression
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T22:52:33.070981+00:00
-- url     : https://prove2.me/theorems/b08f34ca-e432-41ca-a594-ebb8ad6fcd9f
-- title:
--   Pairwise coprime moduli supply persistent CRT walls
-- statement:
--   For B pairwise coprime natural moduli m_i with m_i>B, put P=∏m_i. There is x with B<P≤x<2P such that, whenever every m_i divides an integer L, every predecessor block of length B before x+B+kP is covered by a divisor greater than B common to its point and L, for every k≥0.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L64-L85
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

theorem ErdosProblems.Erdos243.LcmRecordCrossing.exists_crt_covering_progression {B : ℕ} (m : Fin B → ℕ)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x, B < (∏ i, m i) ∧ (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧
      ∀ L : ℤ, (∀ i, (m i : ℤ) ∣ L) → ∀ k : ℕ, ∀ z : ℤ,
        (x + B + k * (∏ i, m i) : ℕ) - (B : ℤ) ≤ z →
        z < (x + B + k * (∏ i, m i) : ℕ) →
        ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by sorry
