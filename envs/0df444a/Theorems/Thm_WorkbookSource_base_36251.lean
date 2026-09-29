-- Prove2me | Theorems.Thm_WorkbookSource_base_36251
-- name    : WorkbookSource.base_36251
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:27.6615+00:00
-- url     : https://prove2.me/theorems/db7a3832-73d1-474a-a92b-ed5bda0b91e2
-- title:
--   A refined squared cyclic ratio inequality
-- statement:
--   Suppose $a,b,c\in \mathbb R^+$ . Prove that : $\left(\frac ab+\frac bc+\frac ca\right)^2\geq (a+b+c)\left(\frac1a+\frac1b+\frac1c\right)+ \frac{(a-b)^2}{bc+ca+ab} . $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36251` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36251; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36251 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) + (a - b) ^ 2 / (b * c + c * a + a * b)  :=  by sorry
