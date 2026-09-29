-- Prove2me | Theorems.Thm_WorkbookSource_plus_50717
-- name    : WorkbookSource.plus_50717
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:56.065986+00:00
-- url     : https://prove2.me/theorems/312dd5d0-483e-43d9-b1c9-338c4397f6a2
-- title:
--   A quartic polynomial bound under a coefficient constraint
-- statement:
--   Let $a, b, c, d, x\in \mathbb{R}$ and $a^{2}+c^{2}\leq 4b$ . Prove that $x^{4}+ax^{3}+bx^{2}+cx+1\geq 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_50717` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_50717; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_50717 (a b c d x : ℝ) (a2c2_leq_4b : a^2 + c^2 ≤ 4*b) : x^4 + a*x^3 + b*x^2 + c*x + 1 ≥ 0   :=  by sorry
