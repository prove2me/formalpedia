-- Prove2me | solution 1 for lean_workbook_plus_36775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:26.171331+00:00
-- url     : https://prove2.me/submissions/0ee88d56-bc57-4a7e-8f94-0f689ecf1256

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℂ)
  (h₀ : a + b + c = 0)
  (h₁ : a * b + b * c + c * a = -19)
  (h₂ : a * b * c = -30) :
  (a + 1) * (b + 1) * (c + 1) = -48 := by
  intros
  grind
