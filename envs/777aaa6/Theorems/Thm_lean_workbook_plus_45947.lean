-- Prove2me | Theorems.Thm_lean_workbook_plus_45947
-- name    : lean_workbook_plus_45947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a34b01eb-e049-4500-a2da-0ddad578836e
-- statement:
--   Show that $\frac{a}{a+3b}+\frac{b}{b+3c}+\frac{c}{c+3d}+\frac{d}{d+3a}<3$ for positive real numbers $a, b, c, d$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45947 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a / (a + 3 * b) + b / (b + 3 * c) + c / (c + 3 * d) + d / (d + 3 * a) < 3   :=  by sorry
