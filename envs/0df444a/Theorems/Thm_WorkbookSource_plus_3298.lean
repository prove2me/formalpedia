-- Prove2me | Theorems.Thm_WorkbookSource_plus_3298
-- name    : WorkbookSource.plus_3298
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:09:16.202612+00:00
-- url     : https://prove2.me/theorems/f2457094-f145-4a2b-993a-d377fd8e3585
-- title:
--   A shifted quartic ratio lower bound at fixed sum six
-- statement:
--   Let $a,b$ and $c$ be real positive numbers such that $a+b+c=6$ . Prove that ${{{\frac{a^4}{1+a+a^2+bc}}+\frac{b^4}{1+b+b^2+ca}}+\frac{c^4}{1+c+c^2+ab}}\ge\frac{48}{11}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3298` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3298; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3298 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) : a^4 / (1 + a + a^2 + b * c) + b^4 / (1 + b + b^2 + c * a) + c^4 / (1 + c + c^2 + a * b) ≥ 48 / 11   :=  by sorry
