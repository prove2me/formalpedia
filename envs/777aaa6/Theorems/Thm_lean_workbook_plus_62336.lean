-- Prove2me | Theorems.Thm_lean_workbook_plus_62336
-- name    : lean_workbook_plus_62336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e36b5939-30b9-48cd-9845-edd4900c0547
-- statement:
--   If there are $n$ possibilities that occur with probabilities $p_1,p_2,p_3,\ldots,p_n$ that are all-encompassing (so $p_1+p_2+\cdots+p_n=1$) that have values $e_1,e_2,e_3,\ldots,e_n$ if they occur, then the expected value is defined as $E=p_1e_1+p_2e_2+\cdots+p_ke_k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62336 {n : ℕ} (p e : Fin n → ℝ) (hp : ∑ i, p i = 1) : ∃ k, ∑ i, p i * e i = k   :=  by sorry
