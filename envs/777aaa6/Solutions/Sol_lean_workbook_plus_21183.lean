-- Prove2me | solution 1 for lean_workbook_plus_21183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:29.653324+00:00
-- url     : https://prove2.me/submissions/7aebfc69-2d6c-4792-befd-95d0699afa76

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℕ, 7 ∣ (3^(2 * n + 1) + 2^(n + 2)) := by
  intro n
  have hbase : (3 : ℕ)^2 ≡ 2 [MOD 7] := by decide
  have hp : 3^(2*n) ≡ 2^n [MOD 7] := by
    rw [pow_mul]
    exact hbase.pow n
  apply Nat.dvd_of_mod_eq_zero
  calc
    (3^(2*n+1)+2^(n+2)) % 7 = (3^(2*n)*3+2^n*4) % 7 := by rw [pow_succ, pow_add]; norm_num
    _ = (2^n*3+2^n*4) % 7 := (hp.mul_right 3).add_right (2^n*4)
    _ = 0 := by
      rw [show 2^n*3+2^n*4 = 7*2^n by ring]
      simp
