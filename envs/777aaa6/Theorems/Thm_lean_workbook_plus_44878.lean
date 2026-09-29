-- Prove2me | Theorems.Thm_lean_workbook_plus_44878
-- name    : lean_workbook_plus_44878
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a4ea265f-d12a-4bf1-ada0-3f25ca184c31
-- statement:
--   Find the sum $\binom{22}{10}\binom{15}{0}+\binom{22}{9}\binom{15}{1}+\binom{22}{8}\binom{15}{2}+\cdots +\binom{22}{0}\binom{15}{10}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44878 (h₁ : 0 < 22) (h₂ : 0 < 15) : ∑ k in Finset.range 11, (Nat.choose 22 (10 - k) * Nat.choose 15 k) = 348330136   :=  by sorry
