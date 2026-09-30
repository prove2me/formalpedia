-- Prove2me | solution 1 for lean_workbook_plus_53067
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:54.483462+00:00
-- url     : https://prove2.me/submissions/f8967868-eed9-4dbf-8b47-9e26e88713e7

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : 2 ^ n ≤ n ^ 3 - 2 * n → n ≥ 2 := by
  intro h
  rcases n with _ | _ | n
  · norm_num at h
  · norm_num at h
  · omega
