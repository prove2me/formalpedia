-- Prove2me | solution 1 for lean_workbook_plus_53894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:49.430606+00:00
-- url     : https://prove2.me/submissions/6bab5271-8262-4c5e-aef2-88dad64641e3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d n : ℤ) (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] := by
  intros
  exact?
