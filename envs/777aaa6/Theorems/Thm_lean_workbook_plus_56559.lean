-- Prove2me | Theorems.Thm_lean_workbook_plus_56559
-- name    : lean_workbook_plus_56559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f114f327-e287-4355-9be6-dbb7ec13ff3e
-- statement:
--   Prove that ${a^2} + ab + {b^2} \ge \frac{3}{4}{(a + b)^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56559 : ∀ a b : ℝ, a^2 + a * b + b^2 ≥ (3 / 4) * (a + b)^2   :=  by sorry
