-- Prove2me | Theorems.Thm_lean_workbook_plus_44165
-- name    : lean_workbook_plus_44165
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c4991b91-bca4-4f5e-bcca-f21ca53684f4
-- statement:
--   $ \Longleftrightarrow 2\cos B\cos C\le 1 - \cos A\ \Longleftrightarrow\ \cos(B + C) + \cos(B - C)\le 1 - \cos A$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44165 : 2 * Real.cos B * Real.cos C ≤ 1 - Real.cos A ↔ Real.cos (B + C) + Real.cos (B - C) ≤ 1 - Real.cos A   :=  by sorry
