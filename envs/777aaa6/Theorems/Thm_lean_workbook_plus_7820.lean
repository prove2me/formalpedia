-- Prove2me | Theorems.Thm_lean_workbook_plus_7820
-- name    : lean_workbook_plus_7820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8b7f1c66-cd24-439e-a1fe-ad0caaa58b8a
-- statement:
--   we have $ a^3\geq a^2$ and $ b^3\geq b^2$ and $ c^3\geq c^2$ because $ a,b,c\geq 1$ then $ a^3+b^3+c^3\geq a^2+b^2+c^2$ and from Am-Gm $ a+b+c\geq 3\sqrt[3]{abc}\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7820  (a b c : ℝ)
  (h₀ : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c) :
  a^3 + b^3 + c^3 ≥ a^2 + b^2 + c^2   :=  by sorry
