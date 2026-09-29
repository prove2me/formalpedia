-- Prove2me | Theorems.Thm_lean_workbook_plus_33256
-- name    : lean_workbook_plus_33256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8ac8bb79-b4d7-42f4-ae25-8cc9f9261bcc
-- statement:
--   Prove that $4(x^2+y^2+z^2) \ge 4(xy+yz+xz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33256 (x y z : ℝ) : 4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x * y + y * z + x * z)   :=  by sorry
