-- Prove2me | solution 1 for lean_workbook_plus_10747
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:20:04.053649+00:00
-- url     : https://prove2.me/submissions/8599c1a5-c7a6-4e51-bd6c-cb9aecc52612

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℕ, ((n-2)*(n-1)*n*(n+1)*(n+2)*(n+3)+3) % 10 = 3 := by
  intro n
  by_cases hsmall : n < 2
  · interval_cases n <;> norm_num
  have hn : 2 ≤ n := by omega
  let m := n-2
  have hnm : n=m+2 := by dsimp [m]; omega
  rw [hnm]
  rw [show m+2-2=m by omega,show m+2-1=m+1 by omega]
  have hmLt := Nat.mod_lt m (by decide : 0 < 10)
  interval_cases hm : m%10 <;> norm_num [Nat.add_mod,Nat.mul_mod,hm]
