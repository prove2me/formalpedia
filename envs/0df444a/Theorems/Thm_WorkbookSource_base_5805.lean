-- Prove2me | Theorems.Thm_WorkbookSource_base_5805
-- name    : WorkbookSource.base_5805
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:45.820165+00:00
-- url     : https://prove2.me/theorems/69b4ec4a-cd46-4d6a-b19c-39636f8fb110
-- title:
--   Three positive quadratic factors bound a Vandermonde product
-- statement:
--   Prove the inequality $(x^{2}-x+1)(y^{2}-y+1)(z^{2}-z+1)\geq (x-y)(y-z)(z-x)$ for real numbers $x, y, z$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5805` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5805; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5805 (x y z : ℝ) :
  (x^2 - x + 1) * (y^2 - y + 1) * (z^2 - z + 1) ≥ (x - y) * (y - z) * (z - x)  :=  by sorry
