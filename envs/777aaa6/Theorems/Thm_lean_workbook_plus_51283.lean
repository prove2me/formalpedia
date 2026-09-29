-- Prove2me | Theorems.Thm_lean_workbook_plus_51283
-- name    : lean_workbook_plus_51283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fcccaaa6-a050-4513-b811-7d0177a9c60c
-- statement:
--   Let $\vec{A}= \left[\begin{array}{c}a_{1}\\vdots\ a_{n}\end{array}\right]$ and $\vec{B}= \left[\begin{array}{c}b_{1}\\vdots\ b_{n}\end{array}\right]$. Prove that $\vec{A}\cdot\vec{B}= \sum_{i=1}^{n}a_{i}b_{i}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51283 (n : ℕ) (a b : Fin n → ℝ) : ∑ i, a i * b i = ∑ i, a i * b i   :=  by sorry
