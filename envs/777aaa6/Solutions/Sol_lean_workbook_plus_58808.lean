-- Prove2me | solution 1 for lean_workbook_plus_58808
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:11.271048+00:00
-- url     : https://prove2.me/submissions/85c2794c-0494-4146-9b7d-7fa655fe1072

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x r y s : ℤ) (q : ℕ) (h₁ : x ≡ r [ZMOD q]) (h₂ : y ≡ s [ZMOD q]) :
  x * y ≡ r * s [ZMOD q] := by
  intros
  exact?
