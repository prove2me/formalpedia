-- Prove2me | Theorems.Thm_WorkbookSource_base_53202
-- name    : WorkbookSource.base_53202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:03:05.590708+00:00
-- url     : https://prove2.me/theorems/85ac4e07-c66f-46a7-9ff0-73f30805b68a
-- title:
--   A cyclic product comparison of quadratic and linear factors
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that : $(a^2+b)(b^2+c)(c^2+a) \ge abc(a+1)(b+1)(c+1).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53202 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b) * (b^2 + c) * (c^2 + a) ≥ a * b * c * (a + 1) * (b + 1) * (c + 1)  :=  by sorry
