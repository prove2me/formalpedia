-- Prove2me | Theorems.Thm_WorkbookSource_base_21812
-- name    : WorkbookSource.base_21812
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:12.599879+00:00
-- url     : https://prove2.me/theorems/826cb9a5-eba1-4e93-bc32-b1c2f19731b8
-- title:
--   A comparison of two weighted cyclic linear ratio sums
-- statement:
--   If $a,b,c$ are positive real numbers,
--    $\sum{\frac{a}{a+2b}}\ge{\sum{\frac{a}{2a+b}}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21812` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21812; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) ≥ (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))  :=  by sorry
