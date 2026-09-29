-- Prove2me | Theorems.Thm_lean_workbook_plus_43022
-- name    : lean_workbook_plus_43022
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/24741cd4-6648-414e-8d92-b9a34a0edf48
-- statement:
--   Find $\lfloor a^6\rfloor$ given that $a$ is a real root of the equation $x^5 - x^3 + x - 2 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43022 (a : ℝ) (ha : a^5 - a^3 + a - 2 = 0) : ⌊a^6⌋ = 3   :=  by sorry
