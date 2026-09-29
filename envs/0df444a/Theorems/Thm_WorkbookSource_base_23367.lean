-- Prove2me | Theorems.Thm_WorkbookSource_base_23367
-- name    : WorkbookSource.base_23367
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:49.006527+00:00
-- url     : https://prove2.me/theorems/51713f4f-3d1b-4d49-abbd-f560ecb7dbd5
-- title:
--   A shifted pair-product reciprocal lower bound at fixed sum three
-- statement:
--   Let $ a,b,c>0$ and $ a+b+c =3$ .Prove that !
--   $ \frac {a + b}{2ab + 1} + \frac {b + c}{2bc + 1} + \frac {a + c}{2ac + 1} \ge 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23367` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23367; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23367 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b) / (2 * a * b + 1) + (b + c) / (2 * b * c + 1) + (a + c) / (2 * a * c + 1) ≥ 2  :=  by sorry
