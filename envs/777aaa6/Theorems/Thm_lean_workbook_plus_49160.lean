-- Prove2me | Theorems.Thm_lean_workbook_plus_49160
-- name    : lean_workbook_plus_49160
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0a939ab0-cf4f-46e5-8234-a401bb5bef31
-- statement:
--   Let $ ax^3 = by^3 = cz^3$ and $ \frac {1}{x} + \frac {1}{y} + \frac {1}{z} = 1$ . Prove that: $ \boxed{\sqrt [3]{ax^2 + by^2 + cz^2} = \sqrt [3]{a} + \sqrt [3]{b} + \sqrt [3]{c}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49160 (a b c x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hab : a * x ^ 3 = b * y ^ 3) (hbc : b * y ^ 3 = c * z ^ 3) (hxyz : 1 / x + 1 / y + 1 / z = 1) : (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) ^ (1 / 3) = (a) ^ (1 / 3) + (b) ^ (1 / 3) + (c) ^ (1 / 3)   :=  by sorry
