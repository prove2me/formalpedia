-- Prove2me | solution 1 for lean_workbook_plus_19255
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:54.375849+00:00
-- url     : https://prove2.me/submissions/8395b01a-aaa0-4899-a0a9-e3542e28960e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) (h₁ : (9 * k + 1) ^ 2 ≡ 10 [ZMOD 27]) : ∃ m : ℕ, k = 3 * m + 2 := by
  have hm : (k:ℤ)%27=0 ∨ (k:ℤ)%27=1 ∨ (k:ℤ)%27=2 ∨ (k:ℤ)%27=3 ∨ (k:ℤ)%27=4 ∨ (k:ℤ)%27=5 ∨ (k:ℤ)%27=6 ∨ (k:ℤ)%27=7 ∨ (k:ℤ)%27=8 ∨ (k:ℤ)%27=9 ∨ (k:ℤ)%27=10 ∨ (k:ℤ)%27=11 ∨ (k:ℤ)%27=12 ∨ (k:ℤ)%27=13 ∨ (k:ℤ)%27=14 ∨ (k:ℤ)%27=15 ∨ (k:ℤ)%27=16 ∨ (k:ℤ)%27=17 ∨ (k:ℤ)%27=18 ∨ (k:ℤ)%27=19 ∨ (k:ℤ)%27=20 ∨ (k:ℤ)%27=21 ∨ (k:ℤ)%27=22 ∨ (k:ℤ)%27=23 ∨ (k:ℤ)%27=24 ∨ (k:ℤ)%27=25 ∨ (k:ℤ)%27=26 := by omega
  have hk : k%3=2 := by
    rcases hm with hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm <;> simp [Int.ModEq,pow_two,Int.add_emod,Int.mul_emod,hm] at h₁ <;> omega
  exact ⟨k/3,by omega⟩
