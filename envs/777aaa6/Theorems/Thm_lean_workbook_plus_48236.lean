-- Prove2me | Theorems.Thm_lean_workbook_plus_48236
-- name    : lean_workbook_plus_48236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a9a12137-dd7a-4db2-953a-4aa20a350004
-- statement:
--   Suppose that $z_1,z_2,\cdots z_n\in{\mathbb{C}}$ then $ |z_1|+|z_2|+\cdots +|z_n|\ge|z_1+z_2+\cdots+z_n|$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48236 : ∀ n : ℕ, ∀ z : Fin n → ℂ, ∑ i, ‖z i‖ ≥ ‖∑ i, z i‖   :=  by sorry
