-- Prove2me | Theorems.Thm_lean_workbook_plus_77590
-- name    : lean_workbook_plus_77590
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f5ce2f69-0df6-41f4-9453-c070d814f00c
-- statement:
--   $2ab+c^2 \ge 2abc(\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}) \Leftrightarrow {{a}^{2}}\left( b+c \right){{\left( c-b \right)}^{2}}+{{b}^{2}}\left( c+a \right){{\left( c-a \right)}^{2}}+\left( a+b \right){{\left( ab-{{c}^{2}} \right)}^{2}}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77590 : ∀ a b c : ℝ,  2 * a * b + c ^ 2 ≥ 2 * a * b * c * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ↔ a ^ 2 * (b + c) * (c - b) ^ 2 + b ^ 2 * (c + a) * (c - a) ^ 2 + (a + b) * (a * b - c ^ 2) ^ 2 ≥ 0   :=  by sorry
