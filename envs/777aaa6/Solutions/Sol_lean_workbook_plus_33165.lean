-- Prove2me | solution 1 for lean_workbook_plus_33165
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:02.291126+00:00
-- url     : https://prove2.me/submissions/5f43bd3d-8686-4b65-b140-4d60ed5d9ee7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k n : ℕ) (h₁ : Even k) (h₂ : Even n) (h₃ : n ≤ k) : 2 * k ≡ n [ZMOD 2 * k - n] := by
  intros
  exact?
