-- Prove2me | Theorems.Thm_WorkbookSource_plus_8538
-- name    : WorkbookSource.plus_8538
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:22.789082+00:00
-- url     : https://prove2.me/theorems/ad0699f7-c860-47f0-a7f7-3d5b9c3eea5e
-- title:
--   A squared cyclic ratio sum bounds a refined reciprocal product
-- statement:
--   Suppose $a,b,c\in \mathbb R^+$ . Prove that : $\left(\frac ab+\frac bc+\frac ca\right)^2\geq (a+b+c)\left(\frac1a+\frac1b+\frac1c\right)+2\cdot \frac{(b-c)^2+(c-a)^2+(a-b)^2}{bc+ca+ab} . $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_8538` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_8538; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_8538 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) + 2 * ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) / (b * c + c * a + a * b)   :=  by sorry
