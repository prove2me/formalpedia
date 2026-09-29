-- Prove2me | Theorems.Thm_lean_workbook_plus_14882
-- name    : lean_workbook_plus_14882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c695a481-f9b4-410b-b4c2-e2079d6edc0d
-- statement:
--   Prove that for $a,b,c,d \in (0,1)$, $b(1-a)+c(1-b)+d(1-c)+a(1-d) \leq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14882 (a b c d : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (hd : 0 < d ∧ d < 1) : b * (1 - a) + c * (1 - b) + d * (1 - c) + a * (1 - d) ≤ 2   :=  by sorry
