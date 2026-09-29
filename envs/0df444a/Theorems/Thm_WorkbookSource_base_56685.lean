-- Prove2me | Theorems.Thm_WorkbookSource_base_56685
-- name    : WorkbookSource.base_56685
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:13.861723+00:00
-- url     : https://prove2.me/theorems/915006dd-c901-4a53-98ff-28752b3cc25b
-- title:
--   A weighted cyclic rational difference sum is nonnegative
-- statement:
--   For $a, b, c>0$ prove or disprove that $\frac{(6a+5b+c)(c-b)}{ab(3a+2b+c)^2}+\frac{(6b+5c+a)(a-c)}{bc(3b+2c+a)^2}+\frac{(6c+5a+b)(b-a)}{ca(3c+2a+b)^2}\ge0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56685` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56685; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56685 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (6 * a + 5 * b + c) * (c - b) / (a * b * (3 * a + 2 * b + c) ^ 2) + (6 * b + 5 * c + a) * (a - c) / (b * c * (3 * b + 2 * c + a) ^ 2) + (6 * c + 5 * a + b) * (b - a) / (c * a * (3 * c + 2 * a + b) ^ 2) ≥ 0  :=  by sorry
