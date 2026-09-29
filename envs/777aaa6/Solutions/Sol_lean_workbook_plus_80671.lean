-- Prove2me | solution 1 for lean_workbook_plus_80671
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:57:31.113097+00:00
-- url     : https://prove2.me/submissions/ac395620-3da5-439b-ba5c-aba3f980be4f

import Mathlib.Tactic

theorem solution : ∀ a : ℝ, (9 / 4 * (a - 1 / 3)^2) ≥ 0 := fun a => by positivity
