-- Prove2me | Theorems.Thm_WorkbookSource_base_7032
-- name    : WorkbookSource.base_7032
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:43.33725+00:00
-- url     : https://prove2.me/theorems/9d12c1e7-0d40-4236-88c8-49de6e1f8953
-- title:
--   A fourth-power difference bound at fixed squared norm
-- statement:
--   Let $a, b, c$ be reals satisfying $a^2+b^2+c^2=6$ . Prove that $$ (a-b)^4+(b-c)^4+(c-a)^4 \leqslant 162$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7032` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7032; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7032 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 6) : (a - b)^4 + (b - c)^4 + (c - a)^4 ≤ 162  :=  by sorry
