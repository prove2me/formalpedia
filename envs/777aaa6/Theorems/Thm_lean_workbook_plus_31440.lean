-- Prove2me | Theorems.Thm_lean_workbook_plus_31440
-- name    : lean_workbook_plus_31440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/58240570-af4e-4543-8ede-a881f1e7f8c8
-- statement:
--   quadratic residues $0,1,4,7$ mod $9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31440 : {0, 1, 4, 7} = {n : ℕ | n < 9 ∧ ∃ k : ℕ, k < 9 ∧ n ≡ k ^ 2 [ZMOD 9]}   :=  by sorry
