-- Prove2me | Theorems.Thm_lean_workbook_plus_21012
-- name    : lean_workbook_plus_21012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f1310027-9d4d-4530-ba1b-cd12b4cad753
-- statement:
--   Prove that $10^{2k} \equiv 1 \pmod{11}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21012 (k : ℕ) : (10^(2 * k)) % 11 = 1   :=  by sorry
