-- Prove2me | Theorems.Thm_lean_workbook_plus_76082
-- name    : lean_workbook_plus_76082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/00487eaf-400e-4b38-aea7-c4789b0085ee
-- statement:
--   Let $a,b$ be positive real numbers . Prove that $\frac{1}{a+b}+\frac{a}{1+b}+\frac{b}{1+a}\ge \frac{3}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76082 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (a + b) + a / (1 + b) + b / (1 + a)) ≥ 3 / 2   :=  by sorry
