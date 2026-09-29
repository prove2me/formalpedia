-- Prove2me | Theorems.Thm_lean_workbook_plus_20976
-- name    : lean_workbook_plus_20976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/04138686-4ae6-417c-b01c-3d5189afc792
-- statement:
--   Prove that $4^{79}$ $<$ $2^{100}+3^{100}$ $<$ $4^{80}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20976 : 4^(79:ℕ) < 2^(100:ℕ) + 3^(100:ℕ) ∧ 2^(100:ℕ) + 3^(100:ℕ) < 4^(80:ℕ)   :=  by sorry
