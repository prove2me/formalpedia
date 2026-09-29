-- Prove2me | Theorems.Thm_lean_workbook_plus_9439
-- name    : lean_workbook_plus_9439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/609abf78-0a9b-4d45-814f-eca97edabedb
-- statement:
--   Let $r,p$ be real numbers. Prove that if $2r + p, r^2 + 2rp, r^2p$ are rational, then $r$ and $p$ are rational.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9439 {r p : ℝ} : (∃ q, 2 * r + p = q) ∧ (∃ q, r ^ 2 + 2 * r * p = q) ∧ (∃ q, r ^ 2 * p = q) → ∃ q, r = q ∧ ∃ q, p = q   :=  by sorry
