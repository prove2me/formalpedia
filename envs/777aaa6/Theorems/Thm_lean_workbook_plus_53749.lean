-- Prove2me | Theorems.Thm_lean_workbook_plus_53749
-- name    : lean_workbook_plus_53749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/40a51c0e-9f8f-4866-8dd2-66035d771f7d
-- statement:
--   Let $a ,b ,c>0 $ and $\frac{b+c}{a}+ \frac{c+a}{b}=12. $ Prove that $$(a+b+c)\left( \frac{1}{a}+\frac{1}{b}+\frac{1}{c} \right) \geq \dfrac{77}{5}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : (b + c) / a + (c + a) / b = 12) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 77 / 5   :=  by sorry
