-- Prove2me | solution 1 for lean_workbook_plus_62015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:17.989887+00:00
-- url     : https://prove2.me/submissions/c8d5aa8c-6d7f-4b4f-8c75-88f860f10875

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k : ℕ) : 3^(2 * (k + 1) + 1) + 2^(k + 3) = 9 * (3^(2 * k + 1) + 2^(k + 2)) - 7 * (2^(k + 2)) := by
  intros
  grind
