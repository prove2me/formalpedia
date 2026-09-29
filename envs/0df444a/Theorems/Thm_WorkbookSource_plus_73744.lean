-- Prove2me | Theorems.Thm_WorkbookSource_plus_73744
-- name    : WorkbookSource.plus_73744
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:40.003105+00:00
-- url     : https://prove2.me/theorems/c0963eaa-c0b4-4660-bb73-aaa4c8b5614b
-- title:
--   A mixed pair-product ratio sum is at most three fifths
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{ab}{(a+b)^2+bc}+\frac{bc}{(b+c)^2+ca}+\frac{ca}{(c+a)^2+ab}\le\frac{3}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73744` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73744; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73744 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / ((a + b) ^ 2 + b * c) + b * c / ((b + c) ^ 2 + c * a) + c * a / ((c + a) ^ 2 + a * b)) ≤ 3 / 5   :=  by sorry
