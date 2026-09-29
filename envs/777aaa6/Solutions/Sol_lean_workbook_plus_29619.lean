-- Prove2me | solution 1 for lean_workbook_plus_29619
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:34.396696+00:00
-- url     : https://prove2.me/submissions/b7c863c5-f84e-4f9f-bec5-3365b1fbf9e9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℕ} (h₁ : a + b = c) : (2^a) * (2^b) = (2^c) := by
  intros
  grind
