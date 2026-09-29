-- Prove2me | solution 1 for lean_workbook_plus_39661
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:16.261128+00:00
-- url     : https://prove2.me/submissions/7d232d38-079d-4041-8e92-4f240ac2092e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b m : ℤ) : a ≡ b [ZMOD m] ↔ m ∣ (a - b) := by
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
