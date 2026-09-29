-- Prove2me | Theorems.Thm_lean_workbook_plus_63276
-- name    : lean_workbook_plus_63276
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0436d61a-d906-4f8e-86ce-4791b0c1e20e
-- statement:
--   If $x,y,z,w\in \left[-\frac{\pi}{2},\frac{\pi}{2}\right]$ such that $\sin x+\sin y+\sin z+\sin w=1$ and $\cos 2x+\cos 2y+\cos 2z+\cos 2w \geq \frac{10}{3}$, then what possible values can $x,y,z,w$ take?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63276 (x y z w : ℝ) (hx : x ∈ Set.Icc (-π/2) (π/2)) (hy : y ∈ Set.Icc (-π/2) (π/2)) (hz : z ∈ Set.Icc (-π/2) (π/2)) (hw : w ∈ Set.Icc (-π/2) (π/2)) (h : sin x + sin y + sin z + sin w = 1) (h' : cos 2*x + cos 2*y + cos 2*z + cos 2*w >= 10/3) : (x = π/2 ∧ y = π/2 ∧ z = -π/2 ∧ w = -π/2) ∨ (x = π/2 ∧ y = -π/2 ∧ z = π/2 ∧ w = -π/2) ∨ (x = π/2 ∧ y = -π/2 ∧ z = -π/2 ∧ w = π/2) ∨ (x = -π/2 ∧ y = π/2 ∧ z = π/2 ∧ w = -π/2) ∨ (x = -π/2 ∧ y = π/2 ∧ z = -π/2 ∧ w = π/2) ∨ (x = -π/2 ∧ y = -π/2 ∧ z = π/2 ∧ w = π/2)   :=  by sorry
