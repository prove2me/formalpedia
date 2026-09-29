-- Prove2me | Theorems.Thm_lean_workbook_plus_79552
-- name    : lean_workbook_plus_79552
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cd8954c7-f427-4e56-8e50-4cd005a1c9de
-- statement:
--   A sequence $(a_n)$ is defined by means of the recursion $a_1 = 1, a_{n+1} = \frac{1 + 4a_n +\sqrt{1+ 24a_n}}{16}.$ Find an explicit formula for $a_n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79552 (a : ℕ → ℚ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16) : ∃ f : ℕ → ℚ, ∀ n, a n = f n   :=  by sorry
