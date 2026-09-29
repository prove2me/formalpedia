-- Prove2me | Theorems.Thm_lean_workbook_plus_39724
-- name    : lean_workbook_plus_39724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4087e673-c274-4378-b106-2eb2eee4e49c
-- statement:
--   Given two natural numbers $a$ and $b$, prove that $\sqrt{ab} <= (a+b)/2 <= \sqrt{a^2+b^2}/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39724 (a b : ℕ) : Real.sqrt (a * b) ≤ (a + b) / 2   :=  by sorry
