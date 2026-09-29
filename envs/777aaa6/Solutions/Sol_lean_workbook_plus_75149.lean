-- Prove2me | solution 1 for lean_workbook_plus_75149
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:27.69444+00:00
-- url     : https://prove2.me/submissions/3f0e2230-a70b-4773-b33f-ed0f9b3ee6f2

import Mathlib.Tactic

theorem solution (z₁ z₂ : ℂ) : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le z₁ z₂
