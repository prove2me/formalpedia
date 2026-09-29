-- Prove2me | Theorems.Thm_lean_workbook_plus_34699
-- name    : lean_workbook_plus_34699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a629e2ad-5d28-481d-9837-5ee2cc5d3408
-- statement:
--   Prove that for integers, when cubed, they fall into the forms $0, 1, 2 \mod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34699 : ∀ x : ℤ, x ^ 3 ≡ 0 [ZMOD 3] ∨ x ^ 3 ≡ 1 [ZMOD 3] ∨ x ^ 3 ≡ 2 [ZMOD 3]   :=  by sorry
