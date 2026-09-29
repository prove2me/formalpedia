-- Prove2me | solution 1 for lean_workbook_plus_18120
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:04.20891+00:00
-- url     : https://prove2.me/submissions/3674c855-d266-462c-98f5-3366ffac50a7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 7 ∣ 3^(2 * n + 1) + 2^(n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases ih with ⟨k,hk⟩
    refine ⟨2*k+3^(2*n+1),?_⟩
    have h1 : 2*(n+1)+1=(2*n+1)+2 := by omega
    have h2 : (n+1)+2=(n+2)+1 := by omega
    simp only [Nat.succ_eq_add_one,h1,h2,pow_add]
    norm_num [pow_add] at hk ⊢
    omega
