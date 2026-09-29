-- Prove2me | Theorems.Thm_lean_workbook_plus_11519
-- name    : lean_workbook_plus_11519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/081274b9-3f68-495e-be53-492d3a7cf7da
-- statement:
--   Then $a_2-a_1 \geq t, a_3-a_1 \geq 2t,...,a_n-a_1 \geq (n-1)t$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11519 (n : ℕ) (a : ℕ → ℝ) (t : ℝ) (h₁ : ∀ i, a (i + 1) - a i ≥ t) : ∀ i, a (i + 1) - a 1 ≥ i * t   :=  by sorry
