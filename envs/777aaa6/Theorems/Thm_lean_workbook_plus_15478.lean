-- Prove2me | Theorems.Thm_lean_workbook_plus_15478
-- name    : lean_workbook_plus_15478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/dd7ebf83-97f9-4fb4-9234-63180532299c
-- statement:
--   And for $1>x>0$ we have $\lfloor x\rfloor =0$ and $0\leq \sqrt{x} <1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15478 : ∀ x : ℝ, 1 > x ∧ x > 0 → ↑⌊x⌋ = 0 ∧ 0 ≤ √x ∧ √x < 1   :=  by sorry
