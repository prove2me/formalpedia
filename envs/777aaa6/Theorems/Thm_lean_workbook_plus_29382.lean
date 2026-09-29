-- Prove2me | Theorems.Thm_lean_workbook_plus_29382
-- name    : lean_workbook_plus_29382
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d920c902-f956-4476-ac38-bccb77d8d07d
-- statement:
--   By Holder, $$\left( \sum_{cyc} \frac{a}{\sqrt{3ab+bc}} \right)^2 \left( \sum_{cyc} a(3ab+bc) \right) \ge (a+b+c)^3$$\n\nSo it suffices to show $$(a+b+c)^3 \ge \frac 94 \sum_{cyc} a(3ab+bc)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29382 : ∀ a b c : ℝ, (a + b + c) ^ 3 ≥ (9 / 4) * (a * (3 * a * b + b * c) + b * (3 * b * c + c * a) + c * (3 * c * a + a * b))   :=  by sorry
