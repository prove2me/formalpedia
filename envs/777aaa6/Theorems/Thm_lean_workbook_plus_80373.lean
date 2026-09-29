-- Prove2me | Theorems.Thm_lean_workbook_plus_80373
-- name    : lean_workbook_plus_80373
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8fade034-9557-4c02-ab3a-cb422a064105
-- statement:
--   Let $a, b$ , and $c$ be real numbers. If $a^3 + b^3 + c^3 = 64$ and $a + b = 0$ , what is the value of $c$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80373 (a b c : ℝ) (h₁ : a^3 + b^3 + c^3 = 64) (h₂ : a + b = 0) : c = 4   :=  by sorry
