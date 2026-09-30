-- Prove2me | solution 1 for lean_workbook_plus_63550
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:50.058439+00:00
-- url     : https://prove2.me/submissions/d7c54dc8-da30-4bfc-b578-f1431f3995df

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution {a b : ℕ} (h : a ∣ b) : a ∣ b := by
  omega
