-- Prove2me | Theorems.Thm_lean_workbook_plus_10058
-- name    : lean_workbook_plus_10058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/09a79ee2-2a4d-4c15-a31c-f5e7f05053d6
-- statement:
--   Prove the following relation: $\forall A,B,C,D \in \mathcal{P}(E) : (A \subset B) \wedge (C \subset D) \Longrightarrow A \cap C \subset B \cap D$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10058 (E : Type) (A B C D : Set E) (h1 : A ⊆ B) (h2 : C ⊆ D) :
  A ∩ C ⊆ B ∩ D   :=  by sorry
