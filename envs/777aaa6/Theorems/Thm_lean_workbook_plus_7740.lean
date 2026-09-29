-- Prove2me | Theorems.Thm_lean_workbook_plus_7740
-- name    : lean_workbook_plus_7740
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5ad08111-c014-4942-bf6e-a3fbee0839e1
-- statement:
--   Prove $P_n = \prod_{k=2}^n \left (1-\frac {1} {k^3}\right ) > \frac {13} {24} > \frac {1} {2}$ for all $n\geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7740 (n : ℕ) (hn : 2 ≤ n) :
  ∏ k in Finset.Icc 2 n, (1 - 1 / k ^ 3) > 13 / 24 ∧ 13 / 24 > 1 / 2   :=  by sorry
