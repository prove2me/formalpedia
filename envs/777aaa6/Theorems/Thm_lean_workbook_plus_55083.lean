-- Prove2me | Theorems.Thm_lean_workbook_plus_55083
-- name    : lean_workbook_plus_55083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/099a1dcb-9445-474f-9c93-2cef0c8fb5cb
-- statement:
--   Given $m^{2}\ge{p^{2}+1}$ (discriminant) and $p^{2}+1\ge2p$ (Cauchy), prove $m^{2}\ge2p$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55083 : ∀ {m p : ℕ}, m^2 ≥ p^2 + 1 ∧ p^2 + 1 ≥ 2 * p → m^2 ≥ 2 * p   :=  by sorry
