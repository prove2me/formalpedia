-- Prove2me | Theorems.Thm_lean_workbook_plus_62573
-- name    : lean_workbook_plus_62573
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/42ad62ff-9b71-4d3b-a15a-92be4563ff94
-- statement:
--   Show that $x^5+x \leq x^6+1$ for $0\leq x\leq \frac{\pi}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62573 ∀ x:ℝ, 0≤ x ∧ x ≤ π/2 → x^5+x ≤ x^6+1   :=  by sorry
