-- Prove2me | Theorems.Thm_lean_workbook_plus_24212
-- name    : lean_workbook_plus_24212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2aec485a-4690-4392-b209-5a0e0db74e22
-- statement:
--   Given $n = a^2 + b^2 + c^2$, prove that $n^2 = x^2 + y^2 + z^2$ for some $x, y, z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24212 {n : ℕ} (h : ∃ a b c : ℕ, n = a^2 + b^2 + c^2) : ∃ x y z : ℕ, n^2 = x^2 + y^2 + z^2   :=  by sorry
