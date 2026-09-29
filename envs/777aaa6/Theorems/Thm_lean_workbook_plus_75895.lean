-- Prove2me | Theorems.Thm_lean_workbook_plus_75895
-- name    : lean_workbook_plus_75895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7ef17a4a-861f-4ab4-827b-bde5cde2ab21
-- statement:
--   Given $d\mid 3ab$ and $(d, ab)=1$, prove that $d\mid 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75895 (d a b : ℤ) (h1 : d ∣ 3 * a * b) (h2 : (d, a * b) = 1) : d ∣ 3   :=  by sorry
