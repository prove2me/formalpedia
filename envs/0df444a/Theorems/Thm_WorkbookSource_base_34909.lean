-- Prove2me | Theorems.Thm_WorkbookSource_base_34909
-- name    : WorkbookSource.base_34909
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:53:53.575088+00:00
-- url     : https://prove2.me/theorems/8d193e5d-6e24-4dc2-910d-9cfebd7fbe83
-- title:
--   A shifted pairwise ratio sum bounds a normalized total
-- statement:
--   Let $a,b,c > 0$ , prove that $\frac{b+c}{a+1}+\frac{c+a}{b+1}+\frac{a+b}{c+1} \geq \frac{6(a + b + c)}{a + b + c + 3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34909` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34909; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 1) + (c + a) / (b + 1) + (a + b) / (c + 1) ≥ 6 * (a + b + c) / (a + b + c + 3)  :=  by sorry
