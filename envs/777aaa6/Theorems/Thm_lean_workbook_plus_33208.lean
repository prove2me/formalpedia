-- Prove2me | Theorems.Thm_lean_workbook_plus_33208
-- name    : lean_workbook_plus_33208
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a2763798-79f4-485d-a51a-b1ea289c5994
-- statement:
--   Denote $\sin(x)=y, \cos(x)=z$ . Then $y^2+z^2=1$ and we have $y^2+3yz-15z^2=0$ and hence $9y^2z^2=(15z^2-y^2)^2$ or, equivalently $9y^2(1-y^2)=(16y^2-15)^2$ which resolves to $265y^4-489y^2+225=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33208  (x : ℝ)
  (y z : ℝ)
  (h₀ : sin x = y)
  (h₁ : cos x = z)
  (h₂ : y^2 + z^2 = 1)
  (h₃ : y^2 + 3 * y * z - 15 * z^2 = 0) :
  9 * y^2 * (1 - y^2) = (16 * y^2 - 15)^2   :=  by sorry
