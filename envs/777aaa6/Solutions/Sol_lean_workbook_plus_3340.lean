-- Prove2me | solution 1 for lean_workbook_plus_3340
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:18.393456+00:00
-- url     : https://prove2.me/submissions/851cb7f0-df73-49f6-a42c-398c47670cdc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p : ℕ) (hp : p.Prime) (a b : ℕ) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  intros
  exact Nat.Prime.dvd_or_dvd hp h
