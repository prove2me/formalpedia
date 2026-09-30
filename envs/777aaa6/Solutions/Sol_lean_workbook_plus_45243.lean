-- Prove2me | solution 1 for lean_workbook_plus_45243
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:34.406825+00:00
-- url     : https://prove2.me/submissions/a40cb7cb-95fb-49e5-b935-1bb673315f97

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (m : ℕ) : Nat.Coprime m (m + 1) := by
  norm_num
