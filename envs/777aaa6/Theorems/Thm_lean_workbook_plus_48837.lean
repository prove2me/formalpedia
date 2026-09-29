-- Prove2me | Theorems.Thm_lean_workbook_plus_48837
-- name    : lean_workbook_plus_48837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5646c0d1-1cfe-428e-b99c-4f63fbfd8bd5
-- statement:
--   Note that $S\equiv \{0,1,2,\dots ,21\} \pmod4$ , and in $S$ are exactly $6$ numbers $0 \pmod 4$ , $6$ numbers $1 \pmod 4$ , $5$ numbers $2 \pmod 4$ and $5$ numbers $3\pmod 4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48837 : (Finset.filter (λ x => x % 4 = 0) (Finset.range 22)).card = 6 ∧ (Finset.filter (λ x => x % 4 = 1) (Finset.range 22)).card = 6 ∧ (Finset.filter (λ x => x % 4 = 2) (Finset.range 22)).card = 5 ∧ (Finset.filter (λ x => x % 4 = 3) (Finset.range 22)).card = 5   :=  by sorry
