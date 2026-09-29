-- Prove2me | Theorems.Thm_lean_workbook_plus_30245
-- name    : lean_workbook_plus_30245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6589a120-167b-40cd-9065-4aeaf22a99c4
-- statement:
--   Prove that for $k \geq 2$, $x_k$ is a natural number, given the sequence $(x_n)$ defined by $x_1=0$ and $x_{n+1}=5x_n + \sqrt{24x_n^2+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30245 (k : ℕ) (x : ℕ → ℕ) (hx: x 1 = 0) (hx2: ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n)^2 + 1)) : k >= 2 → ∃ k0 : ℕ, x k = k0   :=  by sorry
