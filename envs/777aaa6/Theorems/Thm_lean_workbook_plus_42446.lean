-- Prove2me | Theorems.Thm_lean_workbook_plus_42446
-- name    : lean_workbook_plus_42446
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/57943359-9f4d-4474-b887-3462af29ae05
-- statement:
--   I wonder if the set \( \big \{ n \in \mathbb{N} | n=m^2 +1, m \in \mathbb{N} \big \} \) would work.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42446 : ∃ S : Set ℕ, ∀ n, n ∈ S ↔ n = m^2 + 1   :=  by sorry
