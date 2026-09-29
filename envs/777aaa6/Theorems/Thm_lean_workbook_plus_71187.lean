-- Prove2me | Theorems.Thm_lean_workbook_plus_71187
-- name    : lean_workbook_plus_71187
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/985a5377-890a-48ee-b854-42e699a17fed
-- statement:
--   Prove that $2bc + 1 \geq b + c$ given $0 < b, c \leq 1$ using the method $(b-1)(c-1) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71187 (b c : ℝ) (hb : 0 < b ∧ b ≤ 1) (hc : 0 < c ∧ c ≤ 1) : 2 * b * c + 1 ≥ b + c   :=  by sorry
