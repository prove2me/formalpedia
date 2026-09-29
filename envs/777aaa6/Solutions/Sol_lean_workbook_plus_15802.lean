-- Prove2me | solution 1 for lean_workbook_plus_15802
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:55:00.097181+00:00
-- url     : https://prove2.me/submissions/3a5338e6-da07-4d75-ad82-b50f8fc27c71

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) :
  9^(n + 1) - 8 * n - 9 ≡ 0 [ZMOD 64] := by
  induction n with
  | zero => norm_num [Int.ModEq]
  | succ n ih =>
    rw [Int.modEq_iff_dvd] at ih ⊢
    obtain ⟨k,hk⟩ := ih
    refine ⟨9*k-(n:ℤ)-1, ?_⟩
    push_cast
    rw [pow_succ]
    nlinarith [hk]
