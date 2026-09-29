-- Prove2me | Theorems.Thm_lean_workbook_plus_14676
-- name    : lean_workbook_plus_14676
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4660f15f-1181-4f8c-a23b-4429a8d0be24
-- statement:
--   Prove that $sin(x+y)sin(y+z)=sin(y)sin(x+y+z)+sin(z)sin(x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14676 : ∀ x y z : ℝ, sin (x + y) * sin (y + z) = sin y * sin (x + y + z) + sin z * sin x   :=  by sorry
