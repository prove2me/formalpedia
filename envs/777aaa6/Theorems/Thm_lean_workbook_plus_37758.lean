-- Prove2me | Theorems.Thm_lean_workbook_plus_37758
-- name    : lean_workbook_plus_37758
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9f0f5014-a192-43a2-b635-0055cd49d022
-- statement:
--   Prove that $x_1! \cdot x_2! \cdot ... \cdot x_k!~|~(x_1+x_2+...+x_k)!$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37758 (x : ℕ → ℕ) (k : ℕ) :
  ∏ i in Finset.range k, (x i)! ∣ (∑ i in Finset.range k, x i)!   :=  by sorry
