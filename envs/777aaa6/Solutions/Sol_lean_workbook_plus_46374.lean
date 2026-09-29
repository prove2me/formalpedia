-- Prove2me | solution 1 for lean_workbook_plus_46374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:11.039125+00:00
-- url     : https://prove2.me/submissions/f10f905a-ee8e-45a9-847a-325aaef1a155

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ a : ℤ, a ^ 2 ≡ 0 [ZMOD 4] ∨ a ^ 2 ≡ 1 [ZMOD 4] := by
  intro a
  rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left
    apply Int.modEq_zero_iff_dvd.mpr
    exact ⟨k ^ 2, by ring⟩
  · right
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-(k * (k + 1)), by ring⟩
