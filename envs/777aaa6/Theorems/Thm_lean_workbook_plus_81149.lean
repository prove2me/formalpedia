-- Prove2me | Theorems.Thm_lean_workbook_plus_81149
-- name    : lean_workbook_plus_81149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/86c82699-d4de-424c-a7c5-eeae7e570ce0
-- statement:
--   Let $a,b,c,d>0$ . Prove that $3a^2d^2+3b^2c^2+2a^2c^2+2b^2d^2+5abcd \geq 3a^2cd+3d^2ab+3c^2ab+3b^2cd$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81149 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 3 * a ^ 2 * d ^ 2 + 3 * b ^ 2 * c ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * d ^ 2 + 5 * a * b * c * d ≥ 3 * a ^ 2 * c * d + 3 * d ^ 2 * a * b + 3 * c ^ 2 * a * b + 3 * b ^ 2 * c * d   :=  by sorry
