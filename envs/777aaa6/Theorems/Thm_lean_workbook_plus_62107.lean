-- Prove2me | Theorems.Thm_lean_workbook_plus_62107
-- name    : lean_workbook_plus_62107
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/be5aae6a-79d3-48c3-b7af-936527cf58fd
-- statement:
--   Since $n$ is a positive integer, $\lfloor n+\sqrt n+\frac12\rfloor=n+\lfloor \sqrt n+\frac12\rfloor$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62107 (n : ℕ) : ⌊n + Real.sqrt n + 1 / 2⌋ = n + ⌊Real.sqrt n + 1 / 2⌋   :=  by sorry
