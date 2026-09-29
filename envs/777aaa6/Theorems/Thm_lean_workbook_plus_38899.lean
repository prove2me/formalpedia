-- Prove2me | Theorems.Thm_lean_workbook_plus_38899
-- name    : lean_workbook_plus_38899
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3f3e0fe8-3e1b-44bc-8647-7f6a2049eb7a
-- statement:
--   Prove that for all complex numbers $z$ and $w$, $|zw| = |z||w|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38899 (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖   :=  by sorry
