-- Prove2me | solution 1 for lean_workbook_plus_24212
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:25.477247+00:00
-- url     : https://prove2.me/submissions/651d2b59-be61-4aa5-bab2-e5f02d55745f

import Mathlib.Analysis.Complex.Basic

theorem solution {n : ℕ} (h : ∃ a b c : ℕ, n = a^2 + b^2 + c^2) : ∃ x y z : ℕ, n^2 = x^2 + y^2 + z^2 := by
  obtain ⟨a, b, c, rfl⟩ := h
  rcases le_total (c^2) (a^2 + b^2) with hle | hle
  · refine ⟨a^2 + b^2 - c^2, 2 * a * c, 2 * b * c, ?_⟩
    zify [hle]
    ring
  · refine ⟨c^2 - (a^2 + b^2), 2 * a * c, 2 * b * c, ?_⟩
    zify [hle]
    ring
