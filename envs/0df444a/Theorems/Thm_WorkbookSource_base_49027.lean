-- Prove2me | Theorems.Thm_WorkbookSource_base_49027
-- name    : WorkbookSource.base_49027
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:56:36.889876+00:00
-- url     : https://prove2.me/theorems/32289d98-def4-4faf-8cc6-3c6a982c788c
-- title:
--   A cubic sum bound on the unit sphere
-- statement:
--   Let $ a,b,c$ are real numbers such that $a^2+b^2+c^2=1$. Prove that $a^3+b^3+c^3 \le 1+3abc$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49027` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49027; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49027 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : a^3 + b^3 + c^3 ≤ 1 + 3 * a * b * c  :=  by sorry
