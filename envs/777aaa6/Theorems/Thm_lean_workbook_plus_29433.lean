-- Prove2me | Theorems.Thm_lean_workbook_plus_29433
-- name    : lean_workbook_plus_29433
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/72d738ab-6f6e-40a4-973e-ffa15d7fdfb7
-- statement:
--   We must prove that $\sum_{k=0}^{\infty} \frac{(-1)^k}{k!} \cdot \sum_{k=0}^{\infty} \frac{1}{k!}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29433 : (∑' k : ℕ, (-1 : ℝ)^k / k!) * (∑' k : ℕ, 1 / k!) = 1   :=  by sorry
