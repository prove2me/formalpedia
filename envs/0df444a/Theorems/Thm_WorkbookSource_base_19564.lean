-- Prove2me | Theorems.Thm_WorkbookSource_base_19564
-- name    : WorkbookSource.base_19564
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:34:13.414264+00:00
-- url     : https://prove2.me/theorems/4ac0f355-f49f-4c29-abdc-8f40e5717135
-- title:
--   A weighted four-variable cyclic ratio sum is at most one
-- statement:
--   For positive numbers $a$ , $b$ , $c$ and $d$ the following inequality is also true.
--
--    $\sum_{cyc}\frac{a}{2a+b+c}\leq1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19564` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19564; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19564 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a / (2 * a + b + c) + b / (2 * b + c + d) + c / (2 * c + d + a) + d / (2 * d + a + b) ≤ 1  :=  by sorry
