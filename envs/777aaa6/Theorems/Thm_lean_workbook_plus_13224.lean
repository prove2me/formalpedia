-- Prove2me | Theorems.Thm_lean_workbook_plus_13224
-- name    : lean_workbook_plus_13224
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/60abd082-2948-4ac2-af43-72f3695bdfa2
-- statement:
--   Prove: $\sum _{a|b , a>0} \phi (a) =b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13224 (b : ℕ) : ∑ a in b.divisors, φ a = b   :=  by sorry
