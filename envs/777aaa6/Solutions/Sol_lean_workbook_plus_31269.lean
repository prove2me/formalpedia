-- Prove2me | solution 1 for lean_workbook_plus_31269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:14.690401+00:00
-- url     : https://prove2.me/submissions/dd5ef6c8-86e4-4d25-a7bd-2e4d9f3ec86f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨a⁻¹,mul_inv_cancel₀ ha⟩
