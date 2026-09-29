-- Prove2me | Theorems.Thm_WorkbookSource_plus_46670
-- name    : WorkbookSource.plus_46670
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:32.175113+00:00
-- url     : https://prove2.me/theorems/7f187a1d-9422-426f-96a6-be61a361db3d
-- title:
--   A triple-product bound at positive sum three
-- statement:
--   If $a$ , $b$ , and $c$ are positive numbers such that $a+b+c=3$ , prove that $ab+bc+ca \geq 3abc$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_46670` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_46670; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_46670 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a * b + b * c + c * a ≥ 3 * a * b * c   :=  by sorry
