-- Prove2me | Theorems.Thm_lean_workbook_plus_77400
-- name    : lean_workbook_plus_77400
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/74725a19-3045-4aff-95f0-00abe5d04b75
-- statement:
--   Prove, without using calculus, that, for $x > -1$ ,\n\n$x \geq \ln(1+x)$ ,\n\nwith equality if and only if $x=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77400 (x : ℝ) (hx : x > -1) : x ≥ Real.log (1 + x)   :=  by sorry
