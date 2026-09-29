-- Prove2me | Theorems.Thm_lean_workbook_plus_79076
-- name    : lean_workbook_plus_79076
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7a01accd-8691-4a25-b0bc-15de5f85e4f7
-- statement:
--   Prove that if $x^2 \equiv 1 \mod 8$, then $\frac{x^2 - 1}{8}$ is even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79076 : ∀ x : ℤ, x ^ 2 ≡ 1 [ZMOD 8] → Even ((x ^ 2 - 1) / 8)   :=  by sorry
