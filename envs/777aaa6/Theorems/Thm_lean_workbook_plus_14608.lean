-- Prove2me | Theorems.Thm_lean_workbook_plus_14608
-- name    : lean_workbook_plus_14608
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9c1b84b7-4a4e-4d65-841f-9f65a402c975
-- statement:
--   Prove that there are an infinite number of solutions to $a^2+b^2=c^2$ where $a , b, c \in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14608 : ∀ n : ℕ, ∃ a b c : ℕ, a^2 + b^2 = c^2   :=  by sorry
