-- Prove2me | Theorems.Thm_lean_workbook_plus_19781
-- name    : lean_workbook_plus_19781
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4b450af3-171d-4a10-96ee-9f301d8f0f1c
-- statement:
--   Let $x_n = \frac{\pi}{2} - \frac{n\pi}{2\sqrt{n^2 + 1}} = \frac{\pi}{2\sqrt{n^2 + 1}(\sqrt{n^2 + 1} + n)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19781 : ∀ n : ℕ, π / 2 - n * π / (2 * Real.sqrt (n ^ 2 + 1)) = π / (2 * Real.sqrt (n ^ 2 + 1) * (Real.sqrt (n ^ 2 + 1) + n))   :=  by sorry
