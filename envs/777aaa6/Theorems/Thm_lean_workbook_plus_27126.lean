-- Prove2me | Theorems.Thm_lean_workbook_plus_27126
-- name    : lean_workbook_plus_27126
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f3f18c19-b97c-4660-bf49-545dd7acb729
-- statement:
--   Prove by induction that $A^n = \begin{pmatrix}\cos(n\theta) & \sin(n\theta)\\-\sin(n\theta) & \cos(n\theta)\end{pmatrix}$ for $A = \begin{pmatrix}\cos(\theta) & \sin(\theta)\\-\sin(\theta) & \cos(\theta)\end{pmatrix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27126 (A : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (hn: A =!![cos θ, sin θ; -sin θ, cos θ]) : A ^ n =!![cos (n * θ), sin (n * θ); -sin (n * θ), cos (n * θ)]   :=  by sorry
