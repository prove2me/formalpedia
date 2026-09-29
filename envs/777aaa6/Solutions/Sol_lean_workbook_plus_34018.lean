-- Prove2me | solution 1 for lean_workbook_plus_34018
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:54.803867+00:00
-- url     : https://prove2.me/submissions/c5115265-af3a-439e-a96b-326b48f948aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c n : ℤ} (h₁ : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] := by
  intros
  exact?
