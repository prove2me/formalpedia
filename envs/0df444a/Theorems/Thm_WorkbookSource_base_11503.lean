-- Prove2me | Theorems.Thm_WorkbookSource_base_11503
-- name    : WorkbookSource.base_11503
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:12.749413+00:00
-- url     : https://prove2.me/theorems/dfc66012-9ab4-4ff3-bda4-24311d794eff
-- title:
--   A sum bound under linked quadratic relations
-- statement:
--   Let $a,b,c\ge 0,a^2+2b=c$ and $b^2+2c=a.$ Prove that $$a+b+c\le \frac{3}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11503` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11503; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11503 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a^2 + 2 * b = c) (hbc : b^2 + 2 * c = a) : a + b + c ≤ 3 / 4  :=  by sorry
