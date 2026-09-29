-- Prove2me | Theorems.Thm_lean_workbook_plus_35900
-- name    : lean_workbook_plus_35900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/bca0aea4-5e58-4a17-8615-a8c127834817
-- statement:
--   Note that $ (a+b+c)^2-\frac{3}{2}(a(b+c)+b(c+a)+c(a+b)) = \sum \frac{1}{2}(a-b)^2 \geq 0 \ (*)$ , whence it follows that \n\n $ \sum \frac{a}{b+c} = \sum \frac{a^2}{a(b+c)} \geq \frac{(a+b+c)^2}{a(b+c)+b(c+a)+c(a+b)} \geq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35900  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2   :=  by sorry
