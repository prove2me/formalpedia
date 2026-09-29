-- Prove2me | Theorems.Thm_lean_workbook_plus_37716
-- name    : lean_workbook_plus_37716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/79a229c3-3938-4756-89db-3e8c86b78cf5
-- statement:
--   Generalize the property $|cz| = c \cdot |z|$ for any constant $c$ and complex number $z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37716 (c : ℂ) (z : ℂ) : ‖c * z‖ = ‖c‖ * ‖z‖   :=  by sorry
