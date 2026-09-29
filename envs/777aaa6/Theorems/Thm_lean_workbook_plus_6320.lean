-- Prove2me | Theorems.Thm_lean_workbook_plus_6320
-- name    : lean_workbook_plus_6320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3b0defed-29a1-403b-a541-86316eceb922
-- statement:
--   From triangle's inequality we have $b>a-c$ and analogues. Then, the first inequality becomes $\sum{a^2(a-b)(a-c)}\ge 0$, which is Schur for $r=2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6320 :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a + b > c ∧ a + c > b ∧ b + c > a → a^2 * (a - b) * (a - c) + b^2 * (b - a) * (b - c) + c^2 * (c - a) * (c - b) ≥ 0   :=  by sorry
