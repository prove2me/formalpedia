-- Prove2me | solution 1 for lean_workbook_plus_17527
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:09.236706+00:00
-- url     : https://prove2.me/submissions/f24d1afb-e835-4415-941b-69d95689c9f9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (hn : 3 ≤ n) : (17:ℝ)^(n-1) * 2^(n^2) - 1 > 9 * n^2 * 2^(n^2) - 1 := by
  have he : ∀k:ℕ,3≤k → 9*k^2<17^(k-1) := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have he : k=(k-1)+1 := by omega
      change 9*(k+1)^2<17^k
      conv_rhs => rw [he,pow_succ]
      nlinarith [sq_nonneg (k-1)]
  have hh : 9*(n:ℝ)^2<(17:ℝ)^(n-1) := by exact_mod_cast he n hn
  have hp : (0:ℝ)<2^(n^2) := by positivity
  nlinarith [mul_pos (sub_pos.mpr hh) hp]
