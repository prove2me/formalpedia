-- Prove2me | Theorems.Thm_lean_workbook_plus_70216
-- name    : lean_workbook_plus_70216
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/270a7555-c15f-4c0b-8b3e-9972a34d508e
-- statement:
--   Counting the number of handshakes if each person in a room full of n total people shakes hands once with each other person: is there a combinatorial argument that $(1+2+3+...+n)=(n+1) \text{choose} 2$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70216 (n : ℕ) : (∑ i in Finset.range n, i) = n.choose 2   :=  by sorry
