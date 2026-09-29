-- Prove2me | Theorems.Thm_lean_workbook_plus_12100
-- name    : lean_workbook_plus_12100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5cf95ad9-e360-4f12-b3d7-300b3f71e562
-- statement:
--   For $x=1$, prove that $2^n=(1+1)^n = {n \choose 0} + {n \choose 1} + {n \choose 2} + \cdots + {n \choose {n-1}} + {n \choose n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12100 : ∀ n : ℕ, 2 ^ n = ∑ i in Finset.range (n+1), choose n i   :=  by sorry
