-- Prove2me | Theorems.Thm_lean_workbook_plus_14709
-- name    : lean_workbook_plus_14709
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/22750175-af1e-42cf-b7bd-fbbf60cd30fa
-- statement:
--   Let $a, b, c>0$ and $(a+b) (b+c) =4$ . Prove that $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} + \frac{b}{ca} \geq \frac{27}{8}$ (Found by WolframAlpha)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14709 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) = 4) : 1 / a + 1 / b + 1 / c + b / (c * a) ≥ 27 / 8   :=  by sorry
