-- Prove2me | Theorems.Thm_lean_workbook_plus_18356
-- name    : lean_workbook_plus_18356
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4fff5c34-c05c-46fd-8015-2d26c13d0349
-- statement:
--   Prove the identity $(cosh\, x+sinh\, x)^{n}=cosh\, nx+sinh\, nx$ for any real number $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18356 (n x : ℝ) : (cosh x + sinh x)^n = cosh (n*x) + sinh (n*x)   :=  by sorry
