-- Prove2me | Theorems.Thm_lean_workbook_plus_77963
-- name    : lean_workbook_plus_77963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8e1d456e-e159-48db-95b1-fcbb2aba0179
-- statement:
--   Given a chain of n=4 nodes, we have: [geogebra]71ab36900f7feb2dde3081131f5bcd4649af5e59[/geogebra] $ \begin{matrix} a: \ b: \ c: \ d: \end{matrix} \begin{Bmatrix} a & + b & & & = 1 \ a & + b & + c & & = 1 \ & b & + c & + d & = 1 \ & & c & + d & = 1 \end{Bmatrix} \Rightarrow \left\{\begin{matrix} a = 1 \ b = 0 \ c = 0 \ d = 1 \end{matrix}\right.$ Which means we have to hit nodes A and D... right?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77963  (a b c d : ℝ)
  (h₀ : a + b = 1)
  (h₁ : a + b + c = 1)
  (h₂ : b + c + d = 1)
  (h₃ : c + d = 1) :
  a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1   :=  by sorry
