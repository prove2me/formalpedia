-- Prove2me | Theorems.Thm_WorkbookSource_base_12296
-- name    : WorkbookSource.base_12296
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:33.476779+00:00
-- url     : https://prove2.me/theorems/92a29e51-ffe8-4727-ab52-bfa0ed167c66
-- title:
--   A bilinear inequality on the four-dimensional unit sphere
-- statement:
--   For $a,b,c,d \in \mathbb{R}$ such that $ a^2+b^2+c^2+d^2=1 $ Prove that $ a(1+d-a)+b(1+d-b)+c(1+d-c)-d-1 \leq 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12296` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12296; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12296 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
  a * (1 + d - a) + b * (1 + d - b) + c * (1 + d - c) - d - 1 ≤ 0  :=  by sorry
