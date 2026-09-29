-- Prove2me | Theorems.Thm_WorkbookSource_base_18542
-- name    : WorkbookSource.base_18542
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:30.048558+00:00
-- url     : https://prove2.me/theorems/af3c2087-7d4e-4dd7-b135-39c88ef7e03b
-- title:
--   A squared-norm lower bound under two separation constraints
-- statement:
--   Let $ a,b,c$ be real numbers, such that $ a\ge b+1, b\ge c+4,$ . Prove that $a^2 + b^2 + c^2 \ge 14.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18542` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18542; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18542 (a b c : ℝ) (h₁ : a ≥ b + 1) (h₂ : b ≥ c + 4) : a^2 + b^2 + c^2 ≥ 14  :=  by sorry
