-- Prove2me | Theorems.Thm_lean_workbook_plus_80616
-- name    : lean_workbook_plus_80616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1ae3f722-3ac9-45a5-8fa6-a5798bed928e
-- statement:
--   Let $x_1, x_2, \ldots , x_k$ be arbitrary reals. Let $\epsilon > 0$ be given. Then there exists a positive integer $n$ and integers $m_1,m_2, \ldots , m_k$ such that $|nx_i - m_i| < \epsilon$ for all $1 \le i \le m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80616 (k : ℕ) (x : Fin k → ℝ) (ε : ℝ) (ε_pos : ε > 0) : ∃ n : ℕ, ∀ i : Fin k, ∃ m : ℤ, abs (n * x i - m) < ε   :=  by sorry
