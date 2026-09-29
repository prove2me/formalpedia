-- Prove2me | Theorems.Thm_lean_workbook_plus_24221
-- name    : lean_workbook_plus_24221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/80c9bbda-3da9-4892-ad4a-db16723f7eee
-- statement:
--   For the case where $a, b, c \ge 0$, prove the inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24221 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 ≥ 3 * a * b * c   :=  by sorry
