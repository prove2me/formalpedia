-- Prove2me | Theorems.Thm_lean_workbook_plus_26838
-- name    : lean_workbook_plus_26838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e7fe2ccd-30db-46fa-a57c-7d6ea95e6718
-- statement:
--   Count the number of possible outcomes when a coin is flipped \( n \) times and show that it equals \( 2^n \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26838 (n : ℕ) : 2 ^ n = (Finset.card (Finset.univ : Finset (Fin n → Bool)))   :=  by sorry
