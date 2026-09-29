-- Prove2me | solution 1 for lean_workbook_plus_80830
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:34.849663+00:00
-- url     : https://prove2.me/submissions/ba6748fa-48f0-4955-9319-34fe77d4cc84

import Mathlib.Tactic

theorem solution (n : ℕ) : (n+1)^2 = n^2 + 2*n + 1 ∧ (n+1)^2 = n^2 + n + (n+1) := by
  constructor <;> ring
