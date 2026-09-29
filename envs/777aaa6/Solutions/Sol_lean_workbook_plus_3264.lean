-- Prove2me | solution 1 for lean_workbook_plus_3264
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:37.557968+00:00
-- url     : https://prove2.me/submissions/57b87588-37eb-4a70-ae8d-4ae2ca9e2071

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a : ℕ, a ^ 2 ≡ 0 [ZMOD 8] ∨ a ^ 2 ≡ 1 [ZMOD 8] ∨ a ^ 2 ≡ 4 [ZMOD 8] := by
  intro a
  have hm : (a : ℤ)%8=0 ∨ (a : ℤ)%8=1 ∨ (a : ℤ)%8=2 ∨ (a : ℤ)%8=3 ∨ (a : ℤ)%8=4 ∨ (a : ℤ)%8=5 ∨ (a : ℤ)%8=6 ∨ (a : ℤ)%8=7 := by omega
  rcases hm with h|h|h|h|h|h|h|h <;> norm_num [Int.ModEq,pow_two,Int.mul_emod,h]
