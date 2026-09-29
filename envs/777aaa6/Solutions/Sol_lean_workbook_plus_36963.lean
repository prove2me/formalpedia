-- Prove2me | solution 1 for lean_workbook_plus_36963
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:39.826921+00:00
-- url     : https://prove2.me/submissions/96df7bcc-05f6-401b-ba82-bcddc6edc2ac

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x : ℕ) (hab : a ≡ b [ZMOD c]) : a ^ x ≡ b ^ x [ZMOD c] := by
  intros
  exact Int.ModEq.pow x hab
