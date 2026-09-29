-- Prove2me | solution 1 for lean_workbook_plus_45884
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:11:31.453246+00:00
-- url     : https://prove2.me/submissions/5f9592e7-8356-479f-9bd2-c4d757d79593

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℤ} (ha : Odd a) (hb : Odd b) : Odd c → a^2 + b^2 + c^2 ≡ 2 [ZMOD 4] ∨ a^2 + b^2 + c^2 ≡ 3 [ZMOD 4] := by
  have sourceClaim : a^2+b^2+c^2 ≡ 2 [ZMOD 4] ∨
      a^2+b^2+c^2 ≡ 3 [ZMOD 4] := by
    have square4 (t : ℤ) : t^2 % 4 = 0 ∨ t^2 % 4 = 1 := by
      have hlo := Int.emod_nonneg t (by decide : (4:ℤ) ≠ 0)
      have hhi := Int.emod_lt_of_pos t (by decide : (0:ℤ) < 4)
      rw [pow_two,Int.mul_emod]
      interval_cases h : t%4 <;> norm_num [h]
    have oddSquare4 (t : ℤ) (ht : Odd t) : t^2 % 4 = 1 := by
      obtain ⟨k,hk⟩ := ht
      have hid : t^2 = 4*(k^2+k)+1 := by rw [hk]; ring
      rw [hid]
      omega
    have ha4 := oddSquare4 a ha
    have hb4 := oddSquare4 b hb
    rcases square4 c with hc4 | hc4
    · left
      norm_num [Int.ModEq,Int.add_emod,ha4,hb4,hc4]
    · right
      norm_num [Int.ModEq,Int.add_emod,ha4,hb4,hc4]
  intro _
  exact sourceClaim
