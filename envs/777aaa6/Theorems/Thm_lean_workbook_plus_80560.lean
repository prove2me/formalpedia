-- Prove2me | Theorems.Thm_lean_workbook_plus_80560
-- name    : lean_workbook_plus_80560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/747b90a2-ee41-4652-874f-614aa8d558c6
-- statement:
--   With $a;b;c>0$ . Prove: $\sum \dfrac{bc}{a^2+2bc}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80560 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b * c / (a ^ 2 + 2 * b * c) + a * c / (b ^ 2 + 2 * a * c) + a * b / (c ^ 2 + 2 * a * b) ≤ 1)   :=  by sorry
