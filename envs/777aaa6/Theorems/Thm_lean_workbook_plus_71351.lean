-- Prove2me | Theorems.Thm_lean_workbook_plus_71351
-- name    : lean_workbook_plus_71351
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7a6bed6f-5c15-41b1-b422-c7c0c0f465ba
-- statement:
--   Let $a+b=2u$ and $ab=v^2,$ where $v>0$. Prove that $a^2b^2(a^2+b^2-2)\geq (a+b)(ab-1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71351 {a b u v : ℝ} (ha : a > 0) (hb : b > 0) (hv : v > 0) (hab : a + b = 2 * u) (h : a * b = v ^ 2) : a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1)   :=  by sorry
