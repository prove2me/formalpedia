-- Prove2me | Theorems.Thm_lean_workbook_plus_49737
-- name    : lean_workbook_plus_49737
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/347b14d9-9071-4612-9d23-1dd0591bc212
-- statement:
--   Prove that if $d$ divides $n$, then $2^d-1$ divides $2^n-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49737 : ∀ {d n : ℕ}, d ∣ n → (2 ^ d - 1) ∣ (2 ^ n - 1)   :=  by sorry
