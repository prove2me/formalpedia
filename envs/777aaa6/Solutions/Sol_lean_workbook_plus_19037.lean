-- Prove2me | solution 1 for lean_workbook_plus_19037
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:52.526687+00:00
-- url     : https://prove2.me/submissions/07ea157a-418c-41a5-8a93-c7033b9f8202

import Mathlib.Analysis.Complex.Basic

theorem solution {n : ℤ} : (2 * n + 1) ^ 2 - 1 ≡ 0 [ZMOD 8] := by
  have h : (2 * n + 1) ^ 2 - 1 = 4 * (n * (n + 1)) := by ring
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  rw [h, hk]
  exact (Int.modEq_zero_iff_dvd).2 ⟨k, by ring⟩
