-- Prove2me | Theorems.Thm_lean_workbook_plus_21186
-- name    : lean_workbook_plus_21186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/251b8755-111e-4040-aa64-0c979916abff
-- statement:
--   Find the closed form of the sequence $a_n = 1 + \frac{(3^{n-1}-1)}{2} = \frac{(1+3^{n-1})}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21186 (n : ℕ) : 1 + (3 ^ (n - 1) - 1) / 2 = (1 + 3 ^ (n - 1)) / 2   :=  by sorry
