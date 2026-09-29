-- Prove2me | Theorems.Thm_lean_workbook_plus_29233
-- name    : lean_workbook_plus_29233
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/7962aabd-bf64-4f44-a21e-3956a49ef38a
-- statement:
--   $4 \cdot (3+2ab+2ac+2bc) \ge 12(a+b+c) \Leftrightarrow 3+2ab+2ac+2bc \ge 3(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29233 : 4 * (3 + 2 * a * b + 2 * a * c + 2 * b * c) ≥ 12 * (a + b + c) ↔ 3 + 2 * a * b + 2 * a * c + 2 * b * c ≥ 3 * (a + b + c)   :=  by sorry
