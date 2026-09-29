-- Prove2me | Theorems.Thm_lean_workbook_plus_9855
-- name    : lean_workbook_plus_9855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5e55ecd4-6e96-4dcf-aeb5-e11ea75fde32
-- statement:
--   Prove for $a,b>0$ : $\frac{2a}{a+b}+\frac{b}{2a}\ge \frac{1}{2}\left(\frac{a-b}{a+b}\right)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9855 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a / (a + b) + b / (2 * a)) ≥ 1 / 2 * ((a - b) / (a + b)) ^ 2   :=  by sorry
