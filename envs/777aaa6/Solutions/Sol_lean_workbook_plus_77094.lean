-- Prove2me | solution 1 for lean_workbook_plus_77094
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:59:24.366676+00:00
-- url     : https://prove2.me/submissions/b88ad4e0-ee79-47a6-bfdc-0b05405abfea

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ n k : ℕ, n ≤ k → 2^k ∣ 2^n % 10^k) := by
  intro h
  have hbad := h 1 2 (by norm_num)
  norm_num at hbad
