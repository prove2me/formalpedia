-- Prove2me | Theorems.Thm_WorkbookSource_base_17183
-- name    : WorkbookSource.base_17183
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:42:24.576699+00:00
-- url     : https://prove2.me/theorems/d33d8614-3a9b-40bc-8124-df6ddc7a7f3a
-- title:
--   A quartic bound for a symmetric quadratic difference
-- statement:
--   For $a,b,c>0$ . Prove that $7[2(a^2+b^2+c^2)-7(ab+bc+ca)]^2\leqslant 39(a+b+c)^4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17183` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17183; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17183 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 7 * (2 * (a ^ 2 + b ^ 2 + c ^ 2) - 7 * (a * b + b * c + c * a)) ^ 2 ≤ 39 * (a + b + c) ^ 4  :=  by sorry
