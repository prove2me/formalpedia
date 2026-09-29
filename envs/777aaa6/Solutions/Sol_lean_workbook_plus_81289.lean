-- Prove2me | solution 1 for lean_workbook_plus_81289
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:57:16.326496+00:00
-- url     : https://prove2.me/submissions/4e2bb2b4-5fb0-48fe-9d64-ed933a534bc5

import Mathlib.Tactic

theorem solution (a b c d : ℂ) : 2 * (a * c + b * d + c * a + d * b) = 4 * (a * c + b * d) := by ring
