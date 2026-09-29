-- Prove2me | Theorems.Thm_lean_workbook_plus_74197
-- name    : lean_workbook_plus_74197
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/fceb4e5c-7376-4c15-8b23-381b61cd1d6f
-- statement:
--   Given: $\sin (a + b) = \sin a \cos b + \sin b \cos a$ Replace $a$ with $a$ , and $b$ with $-b$ : $\sin (a + -b) = \sin a \cos (-b) + \sin (-b) \cos a$ Simplify using the unit circle: $\sin (a - b) = \sin a \cos b - \sin b \cos a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74197 (a b : ℝ) : sin (a - b) = sin a * cos b - sin b * cos a   :=  by sorry
