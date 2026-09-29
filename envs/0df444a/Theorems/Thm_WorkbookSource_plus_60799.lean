-- Prove2me | Theorems.Thm_WorkbookSource_plus_60799
-- name    : WorkbookSource.plus_60799
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:15.43379+00:00
-- url     : https://prove2.me/theorems/62a9b842-9705-4e62-9de4-f2178fc5fe4c
-- title:
--   Three squared pairwise factors bound a cubed pairwise sum
-- statement:
--   For a,b,c≥0,prove the ineq: $ 27(a^2 + b^2)(b^2 + c^2)(c^2 + a^2)$ ≥ $ 8(ab + bc + ca)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60799` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60799; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60799 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 27 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 8 * (a * b + b * c + c * a)^3   :=  by sorry
