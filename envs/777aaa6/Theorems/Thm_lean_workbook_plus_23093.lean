-- Prove2me | Theorems.Thm_lean_workbook_plus_23093
-- name    : lean_workbook_plus_23093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2acd5073-b648-49aa-b35a-e71d1a2cf725
-- statement:
--   Prove that if $|S| = 2n+1$, then $|S|$ must be odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23093 (n : ℕ) (S : Finset α) (hS : S.card = 2 * n + 1) : Odd S.card   :=  by sorry
