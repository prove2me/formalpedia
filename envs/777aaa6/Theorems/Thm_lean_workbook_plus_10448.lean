-- Prove2me | Theorems.Thm_lean_workbook_plus_10448
-- name    : lean_workbook_plus_10448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/623c4885-489a-435d-9b20-21ee98b5325d
-- statement:
--   For $n=3$, prove that if $0 < a \leq b \leq c$, then $c-a \geq 0$, $c-b \geq 0$, and $b-a \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10448 (a b c : ℝ) (h₁ : 0 < a ∧ a ≤ b ∧ b ≤ c) :
  c - a ≥ 0 ∧ c - b ≥ 0 ∧ b - a ≥ 0   :=  by sorry
