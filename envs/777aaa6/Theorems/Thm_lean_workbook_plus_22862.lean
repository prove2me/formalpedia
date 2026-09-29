-- Prove2me | Theorems.Thm_lean_workbook_plus_22862
-- name    : lean_workbook_plus_22862
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e7940bc5-b1e4-42b8-a812-1ae3063821f0
-- statement:
--   Let $k$ be a positive integer. The sequence $(a_n)_{n \geq 0}$ is defined by $a_0=0$ and $a_{n+1}=(a_n+1)k+(k+1)a_n+2\sqrt{k(k+1)a_n(a_n+1)}, \qquad n=0,1, \ldots.$ Prove that all $a_n$ are positive integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22862 (k : ℕ) (a : ℕ → ℕ) (a0 : a 0 = 0) (a_rec : ∀ n, a (n + 1) = (a n + 1) * k + (k + 1) * a n + 2 * Real.sqrt (k * (k + 1) * a n * (a n + 1))) : ∀ n, 0 < a n   :=  by sorry
