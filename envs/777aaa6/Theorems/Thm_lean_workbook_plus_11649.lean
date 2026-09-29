-- Prove2me | Theorems.Thm_lean_workbook_plus_11649
-- name    : lean_workbook_plus_11649
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4313de54-0f6b-47ac-b890-4ea2300ac61c
-- statement:
--   Given $m=42$ ,denote $S=\{1,2,\cdots,51m\}$ . $A$ is a subset of $S$ ,such that $|A|=50m$ .\nShow that there exist $X,Y\subset S$ such that \n(1) $X\cap Y=Y\cap A=A\cap X=\oslash$ .\n(2) $\sum_{x\in X}x=\sum_{y\in Y}y$ .\n(3) $\sum_{x\in X}x^2=\sum_{y\in Y}y^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11649 (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : S = Finset.Icc 1 (51 * m)) (A : Finset ℕ) (hA : A ⊆ S) (hA' : A.card = 50 * m) : ∃ X Y : Finset ℕ, (X ∩ Y = ∅ ∧ Y ∩ A = ∅ ∧ A ∩ X = ∅ ∧ (∑ x in X, x = ∑ y in Y, y ∧ ∑ x in X, x ^ 2 = ∑ y in Y, y ^ 2))   :=  by sorry
