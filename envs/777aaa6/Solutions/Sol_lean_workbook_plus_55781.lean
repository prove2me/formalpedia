-- Prove2me | solution 1 for lean_workbook_plus_55781
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:32.054982+00:00
-- url     : https://prove2.me/submissions/03687353-6bc3-42b0-9812-7690c52a81a8

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ f : ℕ → ℕ, ∀ n, f n = n + 1 := by
  aesop
