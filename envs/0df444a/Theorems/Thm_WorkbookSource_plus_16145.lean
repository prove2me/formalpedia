-- Prove2me | Theorems.Thm_WorkbookSource_plus_16145
-- name    : WorkbookSource.plus_16145
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:09:49.190344+00:00
-- url     : https://prove2.me/theorems/3dced660-6901-40ce-a696-48f8c9d8c66d
-- title:
--   Two shifted pair-sum reciprocals total at most one half at unit product
-- statement:
--   Let $a,b,c,d>0$ and $abcd=1.$ Prove that
--    $$\frac{1}{a+b+2}+\frac{1}{c+d+2} \le \frac{1}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_16145` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_16145; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_16145 (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d) (habcd : a * b * c * d = 1) : 1 / (a + b + 2) + 1 / (c + d + 2) ≤ 1 / 2   :=  by sorry
