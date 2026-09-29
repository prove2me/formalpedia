-- Prove2me | Theorems.Thm_lean_workbook_plus_3370
-- name    : lean_workbook_plus_3370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/937043c5-23db-4046-9e54-b3471562f908
-- statement:
--   Prove that if $p > 2$ is a prime number, then $2$ divides $p-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3370 (p : ℕ) (hp : p.Prime) (h2 : p > 2) : 2 ∣ p - 1   :=  by sorry
