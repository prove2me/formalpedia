-- Prove2me | Theorems.Thm_lean_workbook_plus_60633
-- name    : lean_workbook_plus_60633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/96a717fe-5516-4e00-aa82-fcaca833e9a0
-- statement:
--   Prove that if $ z_n=a_n+i\cdot b_n$ for $ n=1,2,3,...,k$ .\nThen the inequality is just $ |z_1+z_2+...+z_k|\le |z_1|+|z_2|+...+|z_n|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60633 : ∀ k : ℕ, ∀ z : Fin k → ℂ, ‖∑ i : Fin k, z i‖ ≤ ∑ i : Fin k, ‖z i‖   :=  by sorry
