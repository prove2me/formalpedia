-- Prove2me | Theorems.Thm_lean_workbook_plus_52164
-- name    : lean_workbook_plus_52164
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6562e593-a5c1-4439-9855-5fb32126edcd
-- statement:
--   Prove the formula for the sum of an arithmetic progression: $S = \frac{(dk+2a)(k+1)}{2}$, where $a$ is the first term, $d$ is the common difference, and $k$ is the number of terms.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52164 (a d k : ℕ) : ∑ i in Finset.range (k+1), (a + i * d) = (d * k + 2 * a) * (k + 1) / 2   :=  by sorry
