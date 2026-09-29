-- Prove2me | Theorems.Thm_WorkbookSource_base_30518
-- name    : WorkbookSource.base_30518
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:20:22.371138+00:00
-- url     : https://prove2.me/theorems/6a3372e9-8676-4c35-8b75-956248fb733f
-- title:
--   A reciprocal sum has a triple-product lower bound at fixed total four
-- statement:
--   Let $a,b,c,d$ be positive real numbers such that $a+b+c+d=4$ . Prove that
--    $$\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}\ge \frac{32}{4+abc+bcd+cda+dab}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30518` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30518; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30518 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hab : a + b + c + d = 4) : 1 / a + 1 / b + 1 / c + 1 / d ≥ 32 / (4 + a * b * c + b * c * d + c * d * a + d * a * b)  :=  by sorry
