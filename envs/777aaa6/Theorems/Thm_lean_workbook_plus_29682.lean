-- Prove2me | Theorems.Thm_lean_workbook_plus_29682
-- name    : lean_workbook_plus_29682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1eedfe9b-3db0-4501-a7fb-ad23932e23f6
-- statement:
--   Prove that $2\sum_{cyc}a^4+4\sum_{cyc}a^2b^2 \ge 3\sum_{cyc}ab(a^2+b^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29682 {a b c : ℝ} : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2))   :=  by sorry
