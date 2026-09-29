-- Prove2me | Theorems.Thm_lean_workbook_plus_69781
-- name    : lean_workbook_plus_69781
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/cfa05c23-a4b2-4420-90e0-05752619b415
-- statement:
--   Show that $g(s) = s^{15} + 57s^{14} + 507s^{13} + 1820s^{12} + 4368s^{11} + 8008s^{10} + 11440s^9 + 12870s^8 + 11440s^7 + 8008s^6 + 4368s^5 + 1820s^4 + 560s^3 + 120s^2 + 16s + 1 > 0$ for $s \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69781 (s : ℝ) (hs : 0 ≤ s) : 0 < s^15 + 57 * s^14 + 507 * s^13 + 1820 * s^12 + 4368 * s^11 + 8008 * s^10 + 11440 * s^9 + 12870 * s^8 + 11440 * s^7 + 8008 * s^6 + 4368 * s^5 + 1820 * s^4 + 560 * s^3 + 120 * s^2 + 16 * s + 1   :=  by sorry
