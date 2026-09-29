-- Prove2me | Theorems.Thm_lean_workbook_plus_57775
-- name    : lean_workbook_plus_57775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e25475fa-541b-4db8-a382-c7019b57858f
-- statement:
--   Prove that $ 239^{30} = 1\pmod{31}$ using Fermat's Little Theorem (FLT)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57775 (a : ℕ) : 239 ^ 30 ≡ 1 [ZMOD 31]   :=  by sorry
