-- Prove2me | Theorems.Thm_lean_workbook_plus_43746
-- name    : lean_workbook_plus_43746
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/079457df-fec5-42bb-b970-ebf01d9126ee
-- statement:
--   Write $ {x\over 2} = {m\over n}$ with $ m\in\mathbb{Z},n\in\mathbb{N},\gcd (m,n) = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43746 (x : ℤ) : ∃ m n : ℤ, x / 2 = m / n ∧ m.gcd n = 1   :=  by sorry
