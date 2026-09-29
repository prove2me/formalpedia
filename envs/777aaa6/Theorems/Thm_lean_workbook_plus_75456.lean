-- Prove2me | Theorems.Thm_lean_workbook_plus_75456
-- name    : lean_workbook_plus_75456
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a2b9581c-a24a-41ac-b55e-bab00a5a347d
-- statement:
--   Prove that for any sets A, B, and C, $(A \cap B \cap C)^c = A^c \cup B^c \cup C^c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75456 (A B C : Set α) : (A ∩ B ∩ C)ᶜ = Aᶜ ∪ Bᶜ ∪ Cᶜ   :=  by sorry
