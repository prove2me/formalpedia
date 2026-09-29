-- Prove2me | Theorems.Thm_lean_workbook_plus_53964
-- name    : lean_workbook_plus_53964
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/42a88f1b-dbba-493c-b00b-8c7da4c5198c
-- statement:
--   Given the proof outline for the statement: 'A function $f:A \rightarrow B$ is surjective if and only if for every subset $Z \subset B$, there exists a subset $X \subset A$ such that $f(X) = Z$'. Fill in the details for both directions of the proof.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53964 (f : A → B) : Function.Surjective f ↔ ∀ Z : Set B, ∃ X : Set A, f '' X = Z   :=  by sorry
