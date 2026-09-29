-- Prove2me | solution 1 for lean_workbook_plus_80885
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:19.224584+00:00
-- url     : https://prove2.me/submissions/8046cd00-9628-421f-8093-652472265999

import Mathlib.Tactic

theorem solution (b : ℝ) : b ≠ 0 → 3 * |b| = 3 * |b| := fun _ => rfl
