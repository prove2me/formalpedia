-- Prove2me | Theorems.Thm_lean_workbook_plus_73943
-- name    : lean_workbook_plus_73943
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e026ed37-400e-4317-b72c-0df137cc5412
-- statement:
--   For all real a, b, c prove that:\n\n $$a^4+b^4+c^4+4a^2c^2+4b^2c^2+4c^2a^2+a^2+b^2+c^2 \ge 2a^3(b+c)+2b^3(a+c)+2c^3(a+b)+6abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73943 : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 + 4 * c ^ 2 * a ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * a ^ 3 * (b + c) + 2 * b ^ 3 * (a + c) + 2 * c ^ 3 * (a + b) + 6 * a * b * c   :=  by sorry
