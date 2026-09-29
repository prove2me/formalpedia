-- Prove2me | Theorems.Thm_lean_workbook_plus_64933
-- name    : lean_workbook_plus_64933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/345cdf38-7700-4c75-b532-0a7354d4ed24
-- statement:
--   Hence $(3)\implies b={8a\over 5}$ , so $(2)\implies {13a\over 5}=18\iff a={90\over 13}$ , thus $(1)\implies x={45\over 2}-{90\over 13}={405\over 26}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64933  (a b c x : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 18)
  (h₂ : a + b = 13 / 5 * c)
  (h₃ : b = 8 / 5 * a)
  (h₄ : x = 45 / 2 - 90 / 13) :
  x = 405 / 26   :=  by sorry
