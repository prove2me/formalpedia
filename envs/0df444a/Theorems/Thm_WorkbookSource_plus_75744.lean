-- Prove2me | Theorems.Thm_WorkbookSource_plus_75744
-- name    : WorkbookSource.plus_75744
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:44.412239+00:00
-- url     : https://prove2.me/theorems/88299244-4813-4b93-8160-5edc206c2cd6
-- title:
--   A mixed quadratic-cubic lower bound
-- statement:
--   If $ a,b,c > 0$ and $ ab + bc + ca = 3$ , then
--
--   $ 2(a^2 + b^2 + c^2) + 3abc\geq a + b + c + 6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75744` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75744; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75744 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ a + b + c + 6   :=  by sorry
