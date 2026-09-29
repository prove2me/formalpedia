-- Prove2me | solution 1 for lean_workbook_plus_60748
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:33.881701+00:00
-- url     : https://prove2.me/submissions/e173191c-b1b9-486d-ac19-33a5e9f9b673

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  (3^1959 * (3^64 + 1) / 2 - 2^2023 + 2^2022) = (3^2023 + 3^1959) / 2 - 2^2022 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
