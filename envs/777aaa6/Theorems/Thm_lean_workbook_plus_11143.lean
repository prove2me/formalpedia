-- Prove2me | Theorems.Thm_lean_workbook_plus_11143
-- name    : lean_workbook_plus_11143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/be7eb15c-45df-444d-84a5-cf373397509f
-- statement:
--   What is the value of $p + q + r + s$ when $(p, q, r, s) = (-11, -99, -11, -99)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11143 (p q r s : ℤ) (h₁ : p = -11) (h₂ : q = -99) (h₃ : r = -11) (h₄ : s = -99) : p + q + r + s = -11 - 99 - 11 - 99   :=  by sorry
