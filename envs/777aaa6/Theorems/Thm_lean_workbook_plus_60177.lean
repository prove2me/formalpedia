-- Prove2me | Theorems.Thm_lean_workbook_plus_60177
-- name    : lean_workbook_plus_60177
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0f3cbcc0-e9e1-4633-865d-d6890d98e40c
-- statement:
--   Assume that $a\leqslant b\leqslant c$ . We have: $a^2+b^2+c^2\geqslant ab+bc+ca\Rightarrow \dfrac{a^2+b^2+c^2}{ab+bc+ca}\geqslant \dfrac{2a^2+b^2+c^2}{a^2+ab+bc+ca}=\dfrac{2a^2+b^2+c^2}{(a+b)(a+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60177  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a   :=  by sorry
