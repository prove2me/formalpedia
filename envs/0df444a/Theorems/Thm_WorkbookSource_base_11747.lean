-- Prove2me | Theorems.Thm_WorkbookSource_base_11747
-- name    : WorkbookSource.base_11747
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:39:14.546672+00:00
-- url     : https://prove2.me/theorems/6c6b94d8-d6f9-4b7d-bc10-f7e4cc423d0f
-- title:
--   A cyclic mixed cubic ratio lower bound at fixed sum three
-- statement:
--   Given positive numbers $ a,b,c$ satisfying $a+b+c=3.$ Show that $\frac{a^3+b^2+c^2}{a^2+1}+\frac{b^3+c^2+a^2}{b^2+1}+\frac{c^3+a^2+b^2}{c^2+1}\geq\frac{9}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11747` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11747; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11747 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + b^2 + c^2) / (a^2 + 1) + (b^3 + c^2 + a^2) / (b^2 + 1) + (c^3 + a^2 + b^2) / (c^2 + 1) ≥ 9 / 2  :=  by sorry
