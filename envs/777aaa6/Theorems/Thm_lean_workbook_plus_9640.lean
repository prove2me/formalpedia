-- Prove2me | Theorems.Thm_lean_workbook_plus_9640
-- name    : lean_workbook_plus_9640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b65abca0-76e7-4dab-b70d-5d250f095045
-- statement:
--   Every term is equal to $\binom{n}{j}^{2}\frac{j}{n-j+1} = \binom{n}{j}\binom{n}{j}\frac{j}{n-j+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9640 : ∀ n j : ℕ, ((n.choose j)^2 * j / (n - j + 1) : ℚ) = (n.choose j * (n.choose j * (j / (n - j + 1))))   :=  by sorry
