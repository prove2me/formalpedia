-- Prove2me | Theorems.Thm_lean_workbook_plus_45201
-- name    : lean_workbook_plus_45201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7ee688b8-c89d-4252-b8d9-8efce7be2299
-- statement:
--   Given $a,b,c>0$ . Prove that $\frac{1}{a(b+1)}+\frac{1}{b(c+1)}+\frac{1}{c(a+1)}\ge \frac{3}{1+abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45201 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1))) ≥ 3 / (1 + a * b * c)   :=  by sorry
