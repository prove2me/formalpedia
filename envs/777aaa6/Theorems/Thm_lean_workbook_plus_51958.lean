-- Prove2me | Theorems.Thm_lean_workbook_plus_51958
-- name    : lean_workbook_plus_51958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/509c1e61-32a3-4b82-862e-df1f0d720a53
-- statement:
--   And so $w\equiv x\equiv y\equiv z\pmod {11}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51958  (w x y z : ℕ)
  (h₀ : w ≡ x [ZMOD 11])
  (h₁ : x ≡ y [ZMOD 11])
  (h₂ : y ≡ z [ZMOD 11]) :
  w ≡ z [ZMOD 11]   :=  by sorry
