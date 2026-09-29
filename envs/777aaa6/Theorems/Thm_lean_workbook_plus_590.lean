-- Prove2me | Theorems.Thm_lean_workbook_plus_590
-- name    : lean_workbook_plus_590
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/443454bf-e617-4c8d-83df-cc1a9d30fed2
-- statement:
--   The positive integers $x, y$ and $z$ , where $x < y$ , satisfy $x^{3}+y^{3} = kz^{3}$ , (\*) where $k$ is a given positive integer. In the case $x+y=k$ , show that $z^{3} = k^{2}-3kx +3x^{2}$ . Deduce that $(4z^{3}-k^{2})/3$ is a perfect square and that $\frac{1}{4}k^{2} \leq z^{3} <k^{2}$ . Use these results to find a solution of (\*) when $k=20$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_590 (x y z k : ℤ) (h₁ : 0 < x ∧ 0 < y ∧ 0 < z) (h₂ : x < y) (h₃ : x + y = k) (h₄ : x^3 + y^3 = k * z^3) : z^3 = k^2 - 3 * k * x + 3 * x^2   :=  by sorry
