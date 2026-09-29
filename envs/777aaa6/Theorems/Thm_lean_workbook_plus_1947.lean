-- Prove2me | Theorems.Thm_lean_workbook_plus_1947
-- name    : lean_workbook_plus_1947
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/9b5df54e-a2f6-4323-8301-7ae39d9fd434
-- statement:
--   Prove that a function $f:A \rightarrow B$ is surjective if and only if for every subset $Z \subset B$, there exists a subset $X \subset A$ such that $f(X) = Z$. Use the definition: a function is surjective if for every element $y$ in the codomain, there exists an element in the domain such that $f(x) = y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1947 {f : A → B} : (∀ y : B, ∃ x : A, f x = y) ↔ ∀ Z : Set B, ∃ X : Set A, f '' X = Z   :=  by sorry
