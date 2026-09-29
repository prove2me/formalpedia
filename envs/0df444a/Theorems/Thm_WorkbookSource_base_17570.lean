-- Prove2me | Theorems.Thm_WorkbookSource_base_17570
-- name    : WorkbookSource.base_17570
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:20.241643+00:00
-- url     : https://prove2.me/theorems/086ac12e-4d56-428f-8981-91dc91cb9315
-- title:
--   A difference-product bound with fixed moments
-- statement:
--   Let $x, y,z$ be real numbers such that $x+y+z=1$ and $x^2+y^2+z^2=4$ . Prove that $(y-z)(x-y) \leq \frac{11}{6}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17570` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17570; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17570 (x y z : ℝ) (h1 : x + y + z = 1) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 4) : (y - z) * (x - y) ≤ 11 / 6  :=  by sorry
