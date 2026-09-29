-- Prove2me | Theorems.Thm_lean_workbook_plus_12562
-- name    : lean_workbook_plus_12562
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4779861c-682e-49e0-bb21-841cc97b89fe
-- statement:
--   In general, $\gcd(a,b)=1\ \Leftrightarrow\ ha+kb=1$ for some integers $ h,\,k.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12562 (a b : ℤ) : gcd a b = 1 ↔ ∃ h k : ℤ, h * a + k * b = 1   :=  by sorry
