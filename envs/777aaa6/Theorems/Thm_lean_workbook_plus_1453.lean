-- Prove2me | Theorems.Thm_lean_workbook_plus_1453
-- name    : lean_workbook_plus_1453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/85201846-67c4-47c6-8ced-4da4ba5f84ca
-- statement:
--   Let $ a,b,c \ge 0$ . prove that \n\n $ abc + \frac {13}{3} (a + b + c)^3 \ge \frac {25}{2}(a + b)(b + c)(c + a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1453 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * c + (13/3) * (a + b + c) ^ 3 ≥ (25/2) * (a + b) * (b + c) * (c + a)   :=  by sorry
