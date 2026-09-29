-- Prove2me | Theorems.Thm_lean_workbook_plus_46073
-- name    : lean_workbook_plus_46073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/06ccdee2-0d74-4800-80f9-2f5b4717a89b
-- statement:
--   Thus, $ {\mid z_1\mid}^2 + {\mid z_2\mid}^2 + ... + {\mid z_n\mid}^2 \;\leq\; {\mid w_1\mid}^2 + {\mid w_2\mid}^2 + ... + {\mid w_n\mid}^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46073 (n : ℕ) (w z : Fin n → ℂ) (h : ∀ i, ‖w i‖ = ‖z i‖) : ∑ i, ‖z i‖^2 ≤ ∑ i, ‖w i‖^2   :=  by sorry
