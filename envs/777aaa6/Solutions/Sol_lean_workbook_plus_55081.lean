-- Prove2me | solution 1 for lean_workbook_plus_55081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:23.136811+00:00
-- url     : https://prove2.me/submissions/eff8e3bb-53fc-4b6a-82bb-0f5f61ca3fc5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d m : ℤ) (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m]) : a * c ≡ b * d [ZMOD m] := by
  intros
  exact Int.ModEq.mul h₁ h₂
