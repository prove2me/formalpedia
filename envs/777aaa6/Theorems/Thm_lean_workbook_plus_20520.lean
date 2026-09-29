-- Prove2me | Theorems.Thm_lean_workbook_plus_20520
-- name    : lean_workbook_plus_20520
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d83a6ad9-3c80-4526-beed-abc25b00a5ec
-- statement:
--   Prove that: $(a+b)(b+c)(c+a)+7 \ge 5(a+b+c)$ given $abc=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20520 : a * b * c = 1 → (a + b) * (b + c) * (c + a) + 7 ≥ 5 * (a + b + c)   :=  by sorry
