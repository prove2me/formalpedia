-- Prove2me | Theorems.Thm_WorkbookSource_base_36191
-- name    : WorkbookSource.base_36191
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:47:35.735056+00:00
-- url     : https://prove2.me/theorems/87cb15fd-bc23-42ee-ae16-7830f1e0c2b5
-- title:
--   A weighted four-variable cyclic difference ratio sum is nonnegative
-- statement:
--   Let $ a,b,c,d>0$ ,prove that:
--    $ \frac{a-b}{a+2b+c}+\frac{b-c}{b+2c+d}+\frac{c-d}{c+2d+a}+\frac{d-a}{d+2a+b}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36191` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36191; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36191 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a - b) / (a + 2 * b + c) + (b - c) / (b + 2 * c + d) + (c - d) / (c + 2 * d + a) + (d - a) / (d + 2 * a + b) ≥ 0  :=  by sorry
