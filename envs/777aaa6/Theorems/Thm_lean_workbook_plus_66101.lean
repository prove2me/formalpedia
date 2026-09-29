-- Prove2me | Theorems.Thm_lean_workbook_plus_66101
-- name    : lean_workbook_plus_66101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a0da8a96-bd03-4530-bf33-99141a43873f
-- statement:
--   Prove $a^{3}+b^{3}+c^{3}-3abc=(a+b+c)(a^{2}+b^{2}+c^{2}-ab-ac-bc)$ when $a+b+c=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66101 : ∀ a b c : ℤ, a + b + c = 0 → a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - a * c - b * c)   :=  by sorry
