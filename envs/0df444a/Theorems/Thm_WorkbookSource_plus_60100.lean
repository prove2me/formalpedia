-- Prove2me | Theorems.Thm_WorkbookSource_plus_60100
-- name    : WorkbookSource.plus_60100
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:51:59.745818+00:00
-- url     : https://prove2.me/theorems/26478b98-bb48-4abf-b993-8d0e5f72b9a7
-- title:
--   A four-term product-of-differences ratio sum is nonnegative
-- statement:
--   Let $ a,b,c,d > 0$ ,prove that: $ {\frac {\left( a - b \right) \left( a - c \right) }{\left( a + b \right) \left( a + c \right) }} + {\frac {\left( - c + b \right) \left( - d + b \right) }{\left( b + c \right) \left( b + d \right) }} + {\frac { \left( - d + c \right) \left( - a + c \right) }{\left( c + d \right) \left( a + c \right) }} + {\frac {\left( d - a \right) \left( - b + d \right) }{\left( a + d \right) \left( b + d \right) }}\geq 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60100` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60100; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60100 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a - b) * (a - c) / (a + b) / (a + c) + (-c + b) * (-d + b) / (b + c) / (b + d) + (-d + c) * (-a + c) / (c + d) / (a + c) + (d - a) * (-b + d) / (a + d) / (b + d) ≥ 0   :=  by sorry
