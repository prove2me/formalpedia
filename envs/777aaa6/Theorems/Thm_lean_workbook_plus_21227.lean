-- Prove2me | Theorems.Thm_lean_workbook_plus_21227
-- name    : lean_workbook_plus_21227
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6e6fafa7-e82f-47cb-bc15-e9370f5e85ac
-- statement:
--   2.\quad\prod\sin\frac{A}{2}\le\frac{1}{8}\cos^{2}\frac{B-C}{2}\n\n $\Longleftrightarrow 4\sin\frac{A}{2}\left(\cos\frac{B-C}{2}-\sin\frac{A}{2}\right)\le\cos^{2}\frac{B-C}{2}$\n\n $\Longleftrightarrow\left(\cos\frac{B-C}{2}-2\sin\frac{A}{2}\right)^{2}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21227 :
  ∀ (A B C : ℝ), (Real.pi / 2 < A ∧ Real.pi / 2 < B ∧ Real.pi / 2 < C ∧ A + B + C = Real.pi) →
    Real.sin (A / 2) * Real.sin (B / 2) * Real.sin (C / 2) ≤ (1 / 8) * (Real.cos ((B - C) / 2))^2   :=  by sorry
