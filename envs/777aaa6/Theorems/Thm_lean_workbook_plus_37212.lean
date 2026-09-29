-- Prove2me | Theorems.Thm_lean_workbook_plus_37212
-- name    : lean_workbook_plus_37212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5c2a6c7f-c00f-45e4-9ec8-ca5282ded537
-- statement:
--   If $q$ is an odd integer, prove that either $3q-1$ or $3q+1$ is a multiple of $4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37212 (q : ℤ) (h : q % 2 = 1) : (3 * q - 1) % 4 = 0 ∨ (3 * q + 1) % 4 = 0   :=  by sorry
