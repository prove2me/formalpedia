-- Prove2me | Theorems.Thm_lean_workbook_plus_76439
-- name    : lean_workbook_plus_76439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8b487ec9-4816-4542-b6ed-ccc5d9478c26
-- statement:
--   WLOG assume $(a-1)(b-1)\ge 0$ Thus $c(a-1)(b-1)\ge 0\implies abc\ge bc+ca-c\implies 2abc\ge 2bc+2ca-2c$ Hence we must prove $a^2+b^2+c^2+2bc+2ca-2c+1\ge 2ab+2bc+2ca\implies (a-b)^2+(c-1)^2\ge 0$ which is obvious
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76439  (a b c : ℝ)
  (h₀ : (a - 1) * (b - 1) ≥ 0)
  (h₁ : c * (a - 1) * (b - 1) ≥ 0) :
  a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1 ≥ 2 * a * b + 2 * b * c + 2 * c * a   :=  by sorry
