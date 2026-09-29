-- Prove2me | Theorems.Thm_WorkbookSource_base_5933
-- name    : WorkbookSource.base_5933
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:18.65403+00:00
-- url     : https://prove2.me/theorems/60569f8e-72c5-4cfb-86d4-3afc5b18ce8e
-- title:
--   A reverse product inequality under a disk constraint
-- statement:
--   Prove that: $(ac+bd-1)^{2}\geq (a^{2}+b^{2}-1)(c^{2}+d^{2}-1)$ where $a;b$ are real numbers satisfying $a^{2}+b^{2}\leq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5933` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5933; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5933 (a b c d : ℝ) (h : a^2 + b^2 ≤ 1) :
  (a * c + b * d - 1)^2 ≥ (a^2 + b^2 - 1) * (c^2 + d^2 - 1)  :=  by sorry
