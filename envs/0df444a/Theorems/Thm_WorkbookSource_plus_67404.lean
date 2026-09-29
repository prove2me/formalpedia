-- Prove2me | Theorems.Thm_WorkbookSource_plus_67404
-- name    : WorkbookSource.plus_67404
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:40.835771+00:00
-- url     : https://prove2.me/theorems/c78f46fd-5968-4a93-a824-c878b3f8af35
-- title:
--   A pairwise product ratio sum with a normalized symmetric correction
-- statement:
--   Let $a,b,c>0$ , prove that
--    $\sum {\frac{ab}{ {(a+b)^2}}} + \frac{5}{4} \geq \frac{6(ab+bc+ca)}{(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67404` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67404; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67404 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2 + 5 / 4) ≥ 6 * (a * b + b * c + c * a) / (a + b + c) ^ 2   :=  by sorry
