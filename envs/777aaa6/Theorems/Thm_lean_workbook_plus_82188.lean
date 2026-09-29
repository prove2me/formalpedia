-- Prove2me | Theorems.Thm_lean_workbook_plus_82188
-- name    : lean_workbook_plus_82188
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ac17e1cd-98e7-4de8-ae92-e36ae9815764
-- statement:
--   Thus: $(3a - b - c)(b - c)^2 + (3b - c - a)(c - a)^2 + (3c - a - b)(a - b)^2 \ge (3a - b - c + 3b - c - a)(b - c)^2 + (3c - a - b + 3b - c - a)(a - b)^2 \ge 0$ $\iff$ $ 2(a + b - c)(b - c)^2 + 2(b + c - a)(a - b)^2 \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82188 :
  ∀ a b c : ℝ,
    (3 * a - b - c) * (b - c) ^ 2 + (3 * b - c - a) * (c - a) ^ 2 + (3 * c - a - b) * (a - b) ^ 2 ≥ 0   :=  by sorry
