-- Prove2me | Theorems.Thm_lean_workbook_plus_32948
-- name    : lean_workbook_plus_32948
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/dcd945c8-7248-4664-8cad-f8b09c2aba26
-- statement:
--   $|D_n-n\cdot \ln 2|<\sqrt{n}+1\Leftrightarrow n\cdot \ln 2-\sqrt{n}-1<D_n<n\cdot \ln 2+\sqrt{n}+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32948 (n : ℕ) (D : ℝ) : |D - n * Real.log 2| < Real.sqrt n + 1 ↔ n * Real.log 2 - Real.sqrt n - 1 < D ∧ D < n * Real.log 2 + Real.sqrt n + 1   :=  by sorry
