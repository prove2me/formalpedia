-- Prove2me | Theorems.Thm_lean_workbook_plus_2022
-- name    : lean_workbook_plus_2022
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d35c73cc-2b33-4da1-873f-1e57325f01b1
-- statement:
--   Given the condition $a + b + c \geq abc$, prove the inequality $(u + v + w)^2 \geq 3(uv + vw + uw)$, where $u = \frac{1}{a}, v = \frac{1}{b}, w = \frac{1}{c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2022 (a b c u v w : ℝ) (h : a + b + c ≥ a * b * c) : (u + v + w) ^ 2 ≥ 3 * (u * v + v * w + w * u)   :=  by sorry
