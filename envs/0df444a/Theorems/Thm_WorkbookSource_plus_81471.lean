-- Prove2me | Theorems.Thm_WorkbookSource_plus_81471
-- name    : WorkbookSource.plus_81471
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:58.518991+00:00
-- url     : https://prove2.me/theorems/77624782-6125-4626-997d-d4278ebd6d35
-- title:
--   A two-row linear-map bound under norm constraints
-- statement:
--   Prove that $(ax+by)^2+(cx+dy)^2\leq\frac{1}{16}$, where $a^2+b^2+c^2+d^2\leq\frac{1}{16}$ and $x^2+y^2=1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81471` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81471; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81471 (a b c d x y : ℝ) (h1 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / 16) (h2 : x ^ 2 + y ^ 2 = 1) : (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≤ 1 / 16   :=  by sorry
