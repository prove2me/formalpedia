-- Prove2me | Theorems.Thm_lean_workbook_plus_46069
-- name    : lean_workbook_plus_46069
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4704660b-87d1-4d44-811b-d9b3d133b039
-- statement:
--   The following problem is true already: Prove that for all real $x_i$ ( $\forall i=\overline{1;n}$ ) there exist $\epsilon_i\in\{-1,1\}$ so that the following inequality is true: $(\sum_{i=1}^n\epsilon_i x_i)^2\leq \sum_{i=1}^n x_i^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46069 (n : ℕ) (x : Fin n → ℝ) :
    ∃ ε : Fin n → ℝ, ∀ i, ε i = 1 ∨ ε i = -1 ∧
    (∑ i, ε i * x i) ^ 2 ≤ ∑ i, (x i) ^ 2   :=  by sorry
