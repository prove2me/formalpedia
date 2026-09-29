-- Prove2me | Theorems.Thm_lean_workbook_plus_40887
-- name    : lean_workbook_plus_40887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/db0449d6-65af-48e0-bdc8-c3f627c0dab0
-- statement:
--   If $A = \{1,2,3\}, B = \{2,4,6\}$ and $C = \{1,3,5\}$, then the set $(A \cup B) \cap C$ is
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40887 (A B C : Finset ℕ) : A = {1, 2, 3} ∧ B = {2, 4, 6} ∧ C = {1, 3, 5} → (A ∪ B) ∩ C = {1, 3}   :=  by sorry
