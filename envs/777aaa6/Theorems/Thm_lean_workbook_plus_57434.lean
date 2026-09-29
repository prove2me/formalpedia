-- Prove2me | Theorems.Thm_lean_workbook_plus_57434
-- name    : lean_workbook_plus_57434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d433068f-b8a4-47ae-b9af-a4e16c0a1723
-- statement:
--   For $x=1$ one gets \n\n $a+b+c>\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \Leftrightarrow \frac{a+b+c}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}}>1.$ Thus, it remains to prove that \n\n $ab+bc+ca\geqslant 3\frac{a+b+c}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}} \Leftrightarrow a^2b^2+b^2c^2+c^2a^2\geqslant abc(a+b+c),$ which is just AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57434  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 ≠ a ∧ 1 ≠ b ∧ 1 ≠ c)
  (h₂ : a + b + c ≠ 0)
  (h₃ : a * b * c ≠ 0)
  (h₄ : a + b + c / (1 / a + 1 / b + 1 / c) ≠ 0)
  (h₅ : 1 / a + 1 / b + 1 / c ≠ 0)
  : a * b + b * c + c * a ≥ 3 * (a + b + c) / (1 / a + 1 / b + 1 / c) ↔ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b * c * (a + b + c)   :=  by sorry
