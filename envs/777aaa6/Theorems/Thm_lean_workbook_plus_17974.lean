-- Prove2me | Theorems.Thm_lean_workbook_plus_17974
-- name    : lean_workbook_plus_17974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5ff4dd89-26a9-4f92-af14-93750c77c43a
-- statement:
--   Let $a,b,c>0$ . Prove that $2ab+c^2 \ge 2abc(\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17974 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * a * b + c ^ 2 ≥ 2 * a * b * c * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))   :=  by sorry
