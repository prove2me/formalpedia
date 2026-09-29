-- Prove2me | solution 1 for lean_workbook_plus_76410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:11.631633+00:00
-- url     : https://prove2.me/submissions/f397afd6-25bb-437a-9323-6215832d618e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ {n b c a : ℕ}, n ≡ b [ZMOD c] → n ^ a ≡ b ^ a [ZMOD c] := by
  intros
  exact?
