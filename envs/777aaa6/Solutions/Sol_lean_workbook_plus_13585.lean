-- Prove2me | solution 1 for lean_workbook_plus_13585
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:48:56.566445+00:00
-- url     : https://prove2.me/submissions/304f19db-29c4-4b62-94f1-dd124f06222c

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} : (a - 2 * b + c) ^ 2 ≥ 0 := sq_nonneg _
