-- Prove2me | Theorems.Thm_lean_workbook_plus_80711
-- name    : lean_workbook_plus_80711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d7d8bfe1-edaa-4a44-af4f-ec151b2ed51e
-- statement:
--   If $a,b,c>0\;,$ Then prove that $b^2c^2+c^2a^2+a^2b^2\geq abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : b^2 * c^2 + c^2 * a^2 + a^2 * b^2 ≥ a * b * c * (a + b + c)   :=  by sorry
