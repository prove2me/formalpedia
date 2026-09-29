-- Prove2me | Theorems.Thm_lean_workbook_plus_41801
-- name    : lean_workbook_plus_41801
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/587dbe58-1879-4fc1-9ec4-70ac49fe9b66
-- statement:
--   If $A \cap B = \emptyset $ , where $A$ and $B$ are non-empty sets, then $x \notin B$ , $\forall x \in A$ , or $x \notin A$ , $\forall x \in B$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41801 (A B : Set α) (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A ∩ B = ∅) : (∀ x ∈ A, x ∉ B) ∨ (∀ x ∈ B, x ∉ A)   :=  by sorry
