-- Prove2me | Theorems.Thm_lean_workbook_plus_11505
-- name    : lean_workbook_plus_11505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/708f61d9-44ed-43f0-aab9-068e0a29ce4e
-- statement:
--   Rewrite the expression $4110^{17} \mod 4717$ as $(4110^2)^8 \cdot 4110 \mod 4717$ and use repeated squaring to simplify the calculation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11505 (a : ℕ) : (4110^17) % 4717 = ((4110^2)^8 * 4110) % 4717   :=  by sorry
