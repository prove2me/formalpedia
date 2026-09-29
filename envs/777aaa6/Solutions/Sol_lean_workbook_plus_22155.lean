-- Prove2me | solution 1 for lean_workbook_plus_22155
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:48.266171+00:00
-- url     : https://prove2.me/submissions/780f9ac1-597b-409c-821f-3ba0161fcb90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℕ) (h₁ : b ≠ 0) (h₂ : a ≠ 0) : b ∣ a ↔ ∃ k : ℕ, a = k * b := by
  intros
  exact dvd_iff_exists_eq_mul_left
