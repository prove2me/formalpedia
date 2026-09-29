-- Prove2me | Theorems.Thm_lean_workbook_plus_17553
-- name    : lean_workbook_plus_17553
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f225130e-fe3c-4336-9513-e5d5e3a98fc6
-- statement:
--   Prove that if $p^2 \mid 2^{p+1}$, then $p = 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17553 (p : ℕ) (hp : p.Prime) : p^2 ∣ 2^(p+1) → p = 2   :=  by sorry
