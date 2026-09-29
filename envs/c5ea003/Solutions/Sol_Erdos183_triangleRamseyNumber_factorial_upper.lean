-- Prove2me | solution 1 for Erdos183.triangleRamseyNumber_factorial_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:22:36.873699+00:00
-- url     : https://prove2.me/submissions/e48bf438-0722-489d-af04-08752ac74553

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.NormNum.NatFactorial
import Theorems.Thm_Erdos183_forcesMonochromaticTriangle_succ
import Theorems.Thm_Erdos183_forcesMonochromaticTriangle_zero
import Theorems.Thm_Erdos183_triangleRamseyNumber_forces

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem triangleRamseyNumber_succ_le (k : ℕ) :
    triangleRamseyNumber (k + 1) ≤
      1 + (k + 1) * triangleRamseyNumber k := by
  apply Nat.sInf_le
  exact forcesMonochromaticTriangle_succ (triangleRamseyNumber_forces k)

end Erdos183

open Erdos183

theorem solution (k : ℕ) :
    triangleRamseyNumber k ≤ 4 * k.factorial := by
  have hzero : triangleRamseyNumber 0 ≤ 2 := by
    apply Nat.sInf_le
    exact forcesMonochromaticTriangle_zero
  have hone : triangleRamseyNumber 1 + 1 ≤ 4 := by
    have hrec := triangleRamseyNumber_succ_le 0
    norm_num at hrec ⊢
    omega
  have hstrict : ∀ k : ℕ, 1 ≤ k →
      triangleRamseyNumber k + 1 ≤ 4 * k.factorial := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hzeroj : j = 0
        · subst j
          exact hone
        · have hjpos : 1 ≤ j := by omega
          have hprev := ih hjpos
          have hrec := triangleRamseyNumber_succ_le j
          rw [Nat.factorial_succ]
          nlinarith
  by_cases hk : k = 0
  · subst k
    norm_num
    omega
  · have hbound := hstrict k (by omega)
    omega
