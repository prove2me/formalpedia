-- Prove2me | Theorems.Thm_lean_workbook_plus_41989
-- name    : lean_workbook_plus_41989
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ba3b946d-445f-4978-938b-81fa82852c09
-- statement:
--   prove that $a^3b+a^2bc+c^2ab \ge 3a^2bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41989 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^3 * b + a^2 * b * c + c^2 * a * b ≥ 3 * a^2 * b * c   :=  by sorry
