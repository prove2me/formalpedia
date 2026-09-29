-- Prove2me | Theorems.Thm_lean_workbook_plus_51827
-- name    : lean_workbook_plus_51827
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/63797470-6ef8-4173-85d4-35df24610b6b
-- statement:
--   Prove that $a \equiv 1 \mod c \rightarrow a^n \equiv 1 \mod c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51827 {a n c : ℕ} (h₁ : a ≡ 1 [ZMOD c]) : a ^ n ≡ 1 [ZMOD c]   :=  by sorry
