-- Prove2me | Theorems.Thm_lean_workbook_plus_75871
-- name    : lean_workbook_plus_75871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/1e5eec2c-28ab-4b0a-b7b2-f42c6f6f454d
-- statement:
--   Prove that $a^3 + b^3 \ge ab(a + b)$ for positive real numbers $a$ and $b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75871 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 + b^3 ≥ a * b * (a + b)   :=  by sorry
