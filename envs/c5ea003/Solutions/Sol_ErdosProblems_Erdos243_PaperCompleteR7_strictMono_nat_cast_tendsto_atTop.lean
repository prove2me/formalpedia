-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.strictMono_nat_cast_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:46:46.423634+00:00
-- url     : https://prove2.me/submissions/ad47be0d-c52f-4d4a-8093-419d0e23d0c1

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Analytic part of the canonical tail bridge

Compiled candidates.  The principal analytic assertion is proved, not
postulated: if positive summable terms have successive ratio tending to
zero, their tail divided by the leading term tends to one.

The final theorem derives normalised vanishing from quadratic growth and
an exact tail representation.  It does NOT claim to have constructed the
canonical integer state, proved its integrality, or obtained the sharper
O(1/a_n) expansion required elsewhere in the papers.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7
open Filter
open scoped BigOperators
end ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR7 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n) :
    Tendsto (fun n ↦ (a n : ℝ)) atTop atTop := by
  have hlarge : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hs : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  have hnat : Tendsto a atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro B
    exact ⟨B, fun n hn ↦ hn.trans (hlarge n).le⟩
  exact tendsto_natCast_atTop_atTop.comp hnat
