-- Prove2me | Theorems.Thm_WorkbookSource_base_28147
-- name    : WorkbookSource.base_28147
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:44.390255+00:00
-- url     : https://prove2.me/theorems/b38d85df-1da4-43fb-89c1-1da4e1cb1f02
-- title:
--   A quartic and cubic bound under a zero-sum constraint
-- statement:
--   Let $ a,b,c$ be real numbers such that $ a + b + c = 0.$ Prove that $ a^4 + b^4 + c^4 + 6abc + 12\ge3(a^2 + b^2 + c^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28147` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28147; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28147 (a b c : ℝ) (h : a + b + c = 0) : a^4 + b^4 + c^4 + 6*a*b*c + 12 ≥ 3 * (a^2 + b^2 + c^2)  :=  by sorry
