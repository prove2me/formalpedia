-- Prove2me | Theorems.Thm_lean_workbook_plus_37818
-- name    : lean_workbook_plus_37818
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8938e735-9eab-4323-b03b-33e02ca6c802
-- statement:
--   Prove that among any $ 7$ real numbers there exist two, say $ x$ and $ y$ , such that: $ 0 \le \frac {x - y}{1 + xy} \le \frac {1}{\sqrt {3}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37818 : ∀ S : Finset ℝ, S.card ≥ 7 → ∃ x y, (x : ℝ) ∈ S ∧ (y : ℝ) ∈ S ∧ 0 ≤ (x - y) / (1 + x * y) ∧ (x - y) / (1 + x * y) ≤ 1 / Real.sqrt 3   :=  by sorry
