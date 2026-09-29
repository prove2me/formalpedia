-- Prove2me | Theorems.Thm_lean_workbook_plus_19856
-- name    : lean_workbook_plus_19856
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c97180c7-f2e8-4bb2-bad1-5d17497aa16d
-- statement:
--   Since $\omega$ is a $7$ th root of unity, the numbers $1, \omega, \omega^2, \dots, \omega^6$ are the roots of $x^7-1=0.$ It follows that for all $x,$ $x^7-1=(x-1)(x-\omega)(x-\omega^2)\dots(x-\omega^6).$ Now take $x=2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19856 : 2^7 - 1 = (2 - 1) * (2 - ω) * (2 - ω^2) * (2 - ω^3) * (2 - ω^4) * (2 - ω^5) * (2 - ω^6)   :=  by sorry
