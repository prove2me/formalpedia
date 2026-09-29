-- Prove2me | Theorems.Thm_lean_workbook_plus_71387
-- name    : lean_workbook_plus_71387
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b1240be0-0e99-4896-a100-2aa01a6fea53
-- statement:
--   Prove that $a^{2}+b^{2}+c^{2}+3\geq 2(ab+bc+ac)$ when $abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71387 : a * b * c = 1 → a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a * b + b * c + a * c)   :=  by sorry
