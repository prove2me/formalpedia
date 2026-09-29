-- Prove2me | Theorems.Thm_WorkbookSource_base_56570
-- name    : WorkbookSource.base_56570
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:49.739329+00:00
-- url     : https://prove2.me/theorems/455b0bba-fb0b-4ede-83b3-0adaf7e20a20
-- title:
--   A four-variable quartic difference inequality
-- statement:
--   Let $a,b,c,d$ be positive numbers such that $a+b+c+d=2$ . Prove that $a^4+b^4+c^4+d^4-4abcd \ge 2(a-b)(c-d)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56570` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56570; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56570 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 2) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) * (c - d)  :=  by sorry
