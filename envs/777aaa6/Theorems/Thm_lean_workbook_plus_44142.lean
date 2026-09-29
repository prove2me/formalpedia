-- Prove2me | Theorems.Thm_lean_workbook_plus_44142
-- name    : lean_workbook_plus_44142
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7a8719c8-2782-48f9-8981-3e954ae4e9cc
-- statement:
--   Prove that $4sin\frac{2k\pi}{7}-tan\frac{k\pi}{7}=\left\{ \begin{gathered} \sqrt 7 ( k=1,2,4 )\hfill \ -\sqrt 7 ( k=3,5,6) \hfill \ \end{gathered} \right.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44142 : ∀ k : ℕ, (4 * Real.sin ((2 * k * π) / 7) - Real.tan (k * π / 7)) = if k = 1 ∨ k = 2 ∨ k = 4 then Real.sqrt 7 else (-Real.sqrt 7)   :=  by sorry
