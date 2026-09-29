-- Prove2me | Theorems.Thm_lean_workbook_plus_12507
-- name    : lean_workbook_plus_12507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b354a115-fbbd-4cd7-b683-7d7a6d46220f
-- statement:
--   Let $x+y=a,xy=b$ We need to prove $b^2+a^2+2a+1\geq 2ab+2b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12507 (a b x y : ℝ) (h₁ : x + y = a) (h₂ : x * y = b) : b^2 + a^2 + 2 * a + 1 ≥ 2 * a * b + 2 * b   :=  by sorry
