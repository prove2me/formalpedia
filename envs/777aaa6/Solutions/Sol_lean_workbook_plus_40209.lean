-- Prove2me | solution 1 for lean_workbook_plus_40209
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:11.364439+00:00
-- url     : https://prove2.me/submissions/5853c619-dde7-4de3-8230-c642e47e3374

import Mathlib.Analysis.Complex.Basic

theorem solution {a b : ℤ} (h : a ∣ b) : a^2 ∣ b^2 := by
  rcases h with ⟨k, hk⟩
  refine ⟨k^2, ?_⟩
  rw [hk, mul_pow]
