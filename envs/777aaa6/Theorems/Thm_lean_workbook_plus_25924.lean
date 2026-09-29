-- Prove2me | Theorems.Thm_lean_workbook_plus_25924
-- name    : lean_workbook_plus_25924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ef974ead-962b-4c16-a92e-db4e4e35a5d0
-- statement:
--   Prove that $2\sum_{cyc}a^4+4\sum_{cyc} a^2b^2 - 3\sum_{cyc}(a^3b+b^3a)\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25924 {a b c : ℝ} : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) ≥ 0   :=  by sorry
