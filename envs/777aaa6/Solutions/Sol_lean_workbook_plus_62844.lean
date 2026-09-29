-- Prove2me | solution 1 for lean_workbook_plus_62844
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:13.240695+00:00
-- url     : https://prove2.me/submissions/ddd72477-0fcb-42d6-842d-9e82b6172952

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {d n : ℕ} (h : d ∣ n) (hn : 0 < n) {p : ℕ} (hp : 1 < p) : p^d - 1 ∣ p^n - 1 := by
  intros
  exact Nat.pow_sub_one_dvd_pow_sub_one p h
