-- Prove2me | Theorems.Thm_lean_workbook_plus_36704
-- name    : lean_workbook_plus_36704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/403da246-0010-4c3f-8391-bba83b437196
-- statement:
--   If $ \frac {a}{b - c } + \frac {b}{c - a } + \frac {c}{a - b } = 0$ , prove that $ \frac {a}{(b - c)^2 }$ + $ \frac {b}{(c - a)^2 }$ + $ \frac {c}{(a - b)^2 } = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36704 (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : (a / (b - c) + b / (c - a) + c / (a - b) = 0) → (a / (b - c) ^ 2 + b / (c - a) ^ 2 + c / (a - b) ^ 2 = 0)   :=  by sorry
