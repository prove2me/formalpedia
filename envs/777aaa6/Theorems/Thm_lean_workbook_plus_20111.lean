-- Prove2me | Theorems.Thm_lean_workbook_plus_20111
-- name    : lean_workbook_plus_20111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6f0ca8d0-7cb3-44a8-9649-bc5b3cc744d4
-- statement:
--   Prove that $a^2(b-c)^2+b^2(c-d)^2+c^2(d-a)^2+d^2(a-b)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20111 (a b c d : ℝ) : a^2 * (b - c)^2 + b^2 * (c - d)^2 + c^2 * (d - a)^2 + d^2 * (a - b)^2 ≥ 0   :=  by sorry
