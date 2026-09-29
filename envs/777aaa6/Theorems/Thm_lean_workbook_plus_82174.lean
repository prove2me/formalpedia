-- Prove2me | Theorems.Thm_lean_workbook_plus_82174
-- name    : lean_workbook_plus_82174
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4476aca3-127a-48ec-938f-f0b036fc5c28
-- statement:
--   Expand and simplify $(b - \frac {a}{2})^2 + (c - \frac {a}{2})^2 + (d - \frac {a}{2})^2 + (e - \frac {a}{2})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82174 (a b c d e : ℝ) : (b - a / 2) ^ 2 + (c - a / 2) ^ 2 + (d - a / 2) ^ 2 + (e - a / 2) ^ 2 = b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 - a * (b + c + d + e) + a ^ 2 / 4 * 4   :=  by sorry
