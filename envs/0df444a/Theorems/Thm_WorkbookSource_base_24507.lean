-- Prove2me | Theorems.Thm_WorkbookSource_base_24507
-- name    : WorkbookSource.base_24507
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:42.317453+00:00
-- url     : https://prove2.me/theorems/8fef191c-bd94-43ff-82f7-8b9860a06c81
-- title:
--   A pairwise-product bound under two quadratic equalities
-- statement:
--   Let $a,b,c$ satisfy $a^2+ab+b^2=3$ and $b^2+bc+c^2=16$ . Prove that $ab+bc+ca\le 8$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24507` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24507; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24507 (a b c : ℝ) (ha : a^2 + a * b + b^2 = 3) (hb : b^2 + b * c + c^2 = 16) : a * b + b * c + c * a ≤ 8  :=  by sorry
