-- Prove2me | Theorems.Thm_lean_workbook_plus_24097
-- name    : lean_workbook_plus_24097
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/836a027e-1de2-4e39-9046-98cd1e6787a2
-- statement:
--   You get 1 prompt: \n $\frac{\binom{2}{1}\cdot\binom{4}{2}}{\binom{6}{3}}=\frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24097 :
  ((Nat.choose 2 1 * Nat.choose 4 2) / Nat.choose 6 3) = 3 / 5   :=  by sorry
