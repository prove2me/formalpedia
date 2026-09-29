-- Prove2me | Theorems.Thm_lean_workbook_plus_62911
-- name    : lean_workbook_plus_62911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8230dbe4-bece-4d31-b95e-a42479a6faba
-- statement:
--   Let $ a = \sqrt [3]{11 + \sqrt {337}},\ b = \sqrt [3]{11 - \sqrt {337}}$ , we have $ x = a + b \Longleftrightarrow x -a - b = 0\Longrightarrow x^3 - a^3 - b^3 = 3abx$ , Now $ a^3 + b^3 = 22, ab = 6$ , yielding $ x^3 + 18x = 22$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62911  (x a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b = 6)
  (h₂ : a^3 + b^3 = 22)
  (h₃ : x = a + b) :
  x^3 + 18 * x = 22   :=  by sorry
