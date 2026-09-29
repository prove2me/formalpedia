-- Prove2me | Theorems.Thm_lean_workbook_plus_35004
-- name    : lean_workbook_plus_35004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b449e317-e447-41f4-8ef4-3d0d8adba070
-- statement:
--   Note that for $a,b,c>0$ the sequences $A:=(a,b,c)$ and $B:=(a^2,b^2,c^2)$ . Thus for the rearrangement $C:=(c^2,a^2,b^2)$ of $B$ we have by the REARRANGEMENT inequality: $ A \cdot B \geq A \cdot C \Longleftrightarrow aa^2+bb^2+cc^2\geq ac^2+ba^2+cb^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35004 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * a^2 + b * b^2 + c * c^2 ≥ a * c^2 + b * a^2 + c * b^2   :=  by sorry
