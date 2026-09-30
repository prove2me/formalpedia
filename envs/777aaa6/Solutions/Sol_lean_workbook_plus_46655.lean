-- Prove2me | solution 1 for lean_workbook_plus_46655
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:38.244915+00:00
-- url     : https://prove2.me/submissions/038da78b-14ed-48db-b319-f8a71c2b3c39

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^27653 - 1) % 625 = 491 := by
  omega
