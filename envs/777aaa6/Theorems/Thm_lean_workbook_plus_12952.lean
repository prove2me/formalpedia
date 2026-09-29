-- Prove2me | Theorems.Thm_lean_workbook_plus_12952
-- name    : lean_workbook_plus_12952
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/63ee2126-2ec2-4b3c-8688-3698e03b17de
-- statement:
--   Prove that if $ a > 1$ then $ \frac {1}{a - 1} + \frac {1}{a} + \frac {1}{a + 1} > \frac {3}{a}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12952 (a : ℝ) (h : a > 1) : (a - 1)⁻¹ + a⁻¹ + (a + 1)⁻¹ > 3 * a⁻¹   :=  by sorry
