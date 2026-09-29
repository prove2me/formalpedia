-- Prove2me | solution 1 for lean_workbook_plus_24740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:00.557078+00:00
-- url     : https://prove2.me/submissions/9ea0399d-bbd4-4159-a434-8356c2a8c0f8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c m : ℤ} (h₁ : a ≡ b [ZMOD m]) (h₂ : 0 < m) : (a + c) ≡ (b + c) [ZMOD m] := by
  intros
  exact?
