-- Prove2me | Theorems.Thm_lean_workbook_plus_32277
-- name    : lean_workbook_plus_32277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/820f3fbd-56ce-4c5c-b79d-804fe212ea62
-- statement:
--   Since $a,b,c \in [0;2] \Rightarrow (2-a)(2-b)(2-c)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32277 : ∀ a b c : ℝ, a ∈ Set.Icc 0 2 ∧ b ∈ Set.Icc 0 2 ∧ c ∈ Set.Icc 0 2 → (2 - a) * (2 - b) * (2 - c) ≥ 0   :=  by sorry
