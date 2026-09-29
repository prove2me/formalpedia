-- Prove2me | solution 1 for lean_workbook_plus_40377
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:02.567261+00:00
-- url     : https://prove2.me/submissions/e610799f-78f6-4d29-bcfe-9058bd360fca

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b : ℤ} {p : ℕ} (hp : p.Prime) (h : (p : ℤ) ∣ (a * b)) : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b := by
  intros
  exact Int.Prime.dvd_mul' hp h
