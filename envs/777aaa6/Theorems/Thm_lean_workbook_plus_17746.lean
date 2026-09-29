-- Prove2me | Theorems.Thm_lean_workbook_plus_17746
-- name    : lean_workbook_plus_17746
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/09869330-9af4-426d-8c81-11dd7b7ade49
-- statement:
--   Ugly way: $(a-b)^2(2a^6+5a^4b^2+4a^2b^4+b^6+10a^5b+15a^3b^3+5ab^5+26a^3b^2+13ab^4+27ab^3) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17746 : ∀ a b : ℝ, (a - b) ^ 2 * (2 * a ^ 6 + 5 * a ^ 4 * b ^ 2 + 4 * a ^ 2 * b ^ 4 + b ^ 6 + 10 * a ^ 5 * b + 15 * a ^ 3 * b ^ 3 + 5 * a * b ^ 5 + 26 * a ^ 3 * b ^ 2 + 13 * a * b ^ 4 + 27 * a * b ^ 3) ≥ 0   :=  by sorry
