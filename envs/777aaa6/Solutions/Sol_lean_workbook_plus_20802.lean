-- Prove2me | solution 1 for lean_workbook_plus_20802
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:54:55.516636+00:00
-- url     : https://prove2.me/submissions/18374a48-c552-4f41-a512-74f7d3db459f

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf: f 1 = 1 ∧ ∀ n ≥ 2, n ≥ f n ∧ f n ≥ 2) : ∃ n, n ≥ f n ∧ f n ≥ 2 :=
  ⟨2, hf.2 2 le_rfl⟩
