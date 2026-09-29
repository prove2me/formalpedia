-- Prove2me | solution 1 for lean_workbook_plus_32957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:31.886314+00:00
-- url     : https://prove2.me/submissions/56a0e11f-a9bd-4880-bed8-cfb5344ec277

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ k : ℕ, 8 ^ (2 * k) ≡ 1 [ZMOD 9] ∧ 8 ^ (2 * k + 1) ≡ 8 [ZMOD 9] := by
  intro k
  have h : (8:ℤ)^2 ≡ 1 [ZMOD 9] := by norm_num [Int.ModEq]
  have he : (8:ℤ)^(2*k) ≡ 1 [ZMOD 9] := by simpa [pow_mul] using h.pow k
  constructor
  · exact he
  · simpa [pow_add] using he.mul (Int.ModEq.refl (8:ℤ))
