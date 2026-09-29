-- Prove2me | Theorems.Thm_lean_workbook_plus_40842
-- name    : lean_workbook_plus_40842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/be487192-9986-4d86-95ea-467a984d201d
-- statement:
--   If $ a=15$ and $ b=-9$ , what is the value of $ a^2+2ab+b^2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40842 (a b : ℤ) (h₁ : a = 15) (h₂ : b = -9) : a^2 + 2 * a * b + b^2 = 36   :=  by sorry
