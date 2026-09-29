-- Prove2me | Theorems.Thm_lean_workbook_plus_37272
-- name    : lean_workbook_plus_37272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/622e4b81-afdd-45a3-b679-45c030b2957a
-- statement:
--   Taking $\angle ACD=x$ , and applying 'trig ceva', we have, $f(x)=\frac{sin(x)sin18^{\circ}sin12^{\circ}}{sin(96^{\circ}-x)sin24^{\circ}sin30^{\circ}}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37272 : ∀ x : ℝ, (Real.sin x * Real.sin 18 * Real.sin 12) / (Real.sin (96 - x) * Real.sin 24 * Real.sin 30) = 1   :=  by sorry
