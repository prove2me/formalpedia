-- Prove2me | Theorems.Thm_lean_workbook_plus_36074
-- name    : lean_workbook_plus_36074
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3684e28f-545b-499c-9c26-28df301915e5
-- statement:
--   Let $ a, b, c \in \mathbb{R}$ Prove that $(ab+bc+ca-1)^2 \geq (a^2+1)(b^2+1)(c^2+1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36074 : ∀ a b c : ℝ, (ab + bc + ca - 1) ^ 2 ≥ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)   :=  by sorry
