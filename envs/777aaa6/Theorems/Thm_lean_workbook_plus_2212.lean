-- Prove2me | Theorems.Thm_lean_workbook_plus_2212
-- name    : lean_workbook_plus_2212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2e58478c-166b-4d88-9533-8b08ee0f54e0
-- statement:
--   Prove that: 1) $ x < \lfloor x \rfloor+1$ 2) $ \lceil x \rceil < x+1$ 3) $ \lfloor k+x \rfloor = k+\lfloor x \rfloor$ 4) $ \lfloor x \rfloor =-\lceil-x \rceil$ as well as $ \lceil x \rceil =-\lfloor-x \rceil$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2212 (x : ℝ) (k : ℤ) : (x < ⌊x⌋ + 1) ∧ (⌈x⌉ < x + 1) ∧ (⌊k + x⌋ = k + ⌊x⌋) ∧ (⌊x⌋ = -⌈-x⌉) ∧ (⌈x⌉ = -⌊-x⌋)   :=  by sorry
