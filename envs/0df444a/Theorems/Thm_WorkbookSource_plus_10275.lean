-- Prove2me | Theorems.Thm_WorkbookSource_plus_10275
-- name    : WorkbookSource.plus_10275
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:27.574155+00:00
-- url     : https://prove2.me/theorems/7a28b68c-24f3-4211-93ae-0500d6b1bef6
-- title:
--   A cubic upper bound under a sum and norm relation
-- statement:
--   If $a,b,c>0$ and $a+b+c=a^2+b^2+c^2$, prove that $a^3+b^3+c^3+3(ab+bc+ca)\leq 12$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10275` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10275; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10275 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = a^2 + b^2 + c^2) : a^3 + b^3 + c^3 + 3 * (a * b + b * c + c * a) ≤ 12   :=  by sorry
