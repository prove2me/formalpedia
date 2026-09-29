-- Prove2me | Theorems.Thm_lean_workbook_plus_77010
-- name    : lean_workbook_plus_77010
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b772e588-1fd0-472d-8cb1-3f500e564438
-- statement:
--   Define $P(x) = \prod_{k=2}^n \left ( x+\dfrac {1} {k}\right )$ and $Q(x) = \prod_{k=2}^n \left ( x-\dfrac {1} {k}\right )$ . Then the required sum $S$ is easily seen to fulfill $P(1) + Q(1) = 2(1+S)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77010 (n : ℕ) (hn : 2 ≤ n) (P Q S : ℚ → ℚ) (hP : P = ∏ k in Finset.Icc 2 n, (x + 1/k)) (hQ : Q = ∏ k in Finset.Icc 2 n, (x - 1/k)) (hS : S = (P + Q)/2) : P 1 + Q 1 = 2 * (1 + S 1)   :=  by sorry
