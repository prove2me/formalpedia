-- Prove2me | Theorems.Thm_lean_workbook_plus_68363
-- name    : lean_workbook_plus_68363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c17c033d-2107-4d8d-80ae-d7d0ce82f274
-- statement:
--   Given logical expressions $p \rightarrow s$ and $q \rightarrow s$, both true. Determine if $(p \lor q) \rightarrow s$ is also true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68363 (p q s : Prop) (h₁ : p → s) (h₂ : q → s) : p ∨ q → s   :=  by sorry
