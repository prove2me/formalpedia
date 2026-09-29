-- Prove2me | Theorems.Thm_lean_workbook_plus_8309
-- name    : lean_workbook_plus_8309
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f599b8ff-3be0-42a6-bbdf-6f593e74c212
-- statement:
--   The volume of the $ V-GFN '$ pyramid is $$V_{V-GFN'}= \frac{1}{3} \cdot \frac{GF \cdot FN'}{2} \cdot \sin 60^{\circ} \cdot VF = \frac{1}{3} \cdot \frac{\frac{9k}{2} \cdot 3k}{2}\cdot \frac{\sqrt{3}}{2} \cdot 9k = \frac{81 \sqrt{3}}{8} k^3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8309 (k : ℝ) : (1 / 3 * (9 * k / 2 * 3 * k / 2) * Real.sqrt 3 / 2 * 9 * k) = 81 * Real.sqrt 3 / 8 * k ^ 3   :=  by sorry
