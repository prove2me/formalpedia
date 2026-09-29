-- Prove2me | solution 1 for lean_workbook_plus_61497
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:26.542056+00:00
-- url     : https://prove2.me/submissions/9d62dcdc-b7e9-4687-917f-b892019ccec9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p : ℕ) (b c : ℕ) (hp : p.Prime) (h : p ∣ b * c) : p ∣ b ∨ p ∣ c := by
  intros
  exact?
