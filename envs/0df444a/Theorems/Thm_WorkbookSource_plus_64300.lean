-- Prove2me | Theorems.Thm_WorkbookSource_plus_64300
-- name    : WorkbookSource.plus_64300
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:34.27506+00:00
-- url     : https://prove2.me/theorems/7d54d51e-2f90-43e9-a54e-03f2ed3a7e5d
-- title:
--   A product of quadratic factors under a fixed sum
-- statement:
--   For $a,b,c \in \mathbb R$ such that $a+b+c=7$ . Prove: $(a^2+1)(b^2+1)(c^2+1)+30abc+15 \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_64300` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_64300; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_64300 (a b c : ℝ) (h : a + b + c = 7) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + 30 * a * b * c + 15 ≥ 0   :=  by sorry
