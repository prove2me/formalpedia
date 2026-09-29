-- Prove2me | Theorems.Thm_lean_workbook_plus_47613
-- name    : lean_workbook_plus_47613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d23a3ba2-8802-4ceb-b3e9-67f029d256e6
-- statement:
--   Prove $2k+2 \leq 2^{k}$ for $k \ge 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47613 (k : ℕ) (h₁ : 3 ≤ k) : 2 * k + 2 ≤ 2^k   :=  by sorry
