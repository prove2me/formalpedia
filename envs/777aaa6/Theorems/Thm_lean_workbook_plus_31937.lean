-- Prove2me | Theorems.Thm_lean_workbook_plus_31937
-- name    : lean_workbook_plus_31937
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6623f94d-83d4-4f2d-97e9-0058f96909ac
-- statement:
--   Prove the following inequality: $\frac{a^2+3bc}{(b+c)^2}+\frac{b^2+3ca}{(c+a)^2}+\frac{c^2+3ab}{(a+b)^2} \ge \frac{11}{4}+\frac{2abc}{(a+b)(b+c)(c+a)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31937 : ∀ a b c : ℝ, (a^2 + 3 * b * c) / (b + c)^2 + (b^2 + 3 * c * a) / (c + a)^2 + (c^2 + 3 * a * b) / (a + b)^2 ≥ 11 / 4 + 2 * a * b * c / (a + b) / (b + c) / (c + a)   :=  by sorry
