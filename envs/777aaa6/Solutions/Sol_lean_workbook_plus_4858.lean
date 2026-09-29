-- Prove2me | solution 1 for lean_workbook_plus_4858
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:07.741195+00:00
-- url     : https://prove2.me/submissions/17717541-8fe6-423d-88a6-bc232e477627

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b n : ℤ, a ≡ b [ZMOD n] → n ∣ (a - b) := by
  intro a b n
  intros
  exact?
