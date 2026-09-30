-- Prove2me | solution 1 for lean_workbook_plus_57055
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:41.271609+00:00
-- url     : https://prove2.me/submissions/144240f0-5097-4466-b6e6-1d7b5caf4428

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (m n : ℤ) (h : 13 ∣ (m + n)) : 13 ∣ (m^3 + n^3) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k * (m^2 - m*n + n^2), ?_⟩
  calc
    m^3 + n^3 = (m+n) * (m^2 - m*n + n^2) := by ring
    _ = 13 * (k * (m^2 - m*n + n^2)) := by rw [hk]; ring
