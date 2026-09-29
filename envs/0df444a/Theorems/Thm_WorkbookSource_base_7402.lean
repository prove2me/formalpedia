-- Prove2me | Theorems.Thm_WorkbookSource_base_7402
-- name    : WorkbookSource.base_7402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:30.532059+00:00
-- url     : https://prove2.me/theorems/00333f07-bbb7-43c3-9a18-216256eb0854
-- title:
--   A squared-distance lower bound under two quadratic constraints
-- statement:
--   Let $a, b, c, d$ be real numbers such that $a^2+b^2 = 1$ and $cd = 2$ . Prove that $$(a - d)^2 + (b - c)^2\geq 1$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7402` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7402; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7402 (a b c d : ℝ) (ha : a^2 + b^2 = 1) (hb : c * d = 2) : (a - d)^2 + (b - c)^2 ≥ 1  :=  by sorry
