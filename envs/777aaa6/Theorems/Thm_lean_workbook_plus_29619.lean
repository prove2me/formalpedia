-- Prove2me | Theorems.Thm_lean_workbook_plus_29619
-- name    : lean_workbook_plus_29619
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/84c7538e-690d-49e1-a026-584012d6720c
-- statement:
--   If $a + b = c$, prove that $2^a \times 2^b = 2^c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29619 {a b c : ℕ} (h₁ : a + b = c) : (2^a) * (2^b) = (2^c)   :=  by sorry
