-- Prove2me | Theorems.Thm_lean_workbook_plus_31177
-- name    : lean_workbook_plus_31177
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/06d3a222-d5f5-452d-8975-70af7c7f723f
-- statement:
--   Show that \(\frac{\sin x+\sin y}{2}=\sin\frac{x+y}{2}\cos\frac{x-y}{2}\le\sin\frac{x+y}{2}\) for all \( x,\,y\in [0;\,\pi] \).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31177 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ π) (hy : 0 ≤ y ∧ y ≤ π) :
  sin ((x + y) / 2) * cos ((x - y) / 2) ≤ sin ((x + y) / 2)   :=  by sorry
