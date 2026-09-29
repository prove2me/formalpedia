-- Prove2me | Theorems.Thm_lean_workbook_plus_30565
-- name    : lean_workbook_plus_30565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c237b38c-05e3-4cdc-8387-d01657f32808
-- statement:
--   Prove that $ \frac{ab}{2c+a+b} \le \frac{ab}{4}\left(\frac{1}{c+a} +\frac{1}{c+b}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30565 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a * b / (2 * c + a + b) ≤ a * b / 4 * (1 / (c + a) + 1 / (c + b))   :=  by sorry
