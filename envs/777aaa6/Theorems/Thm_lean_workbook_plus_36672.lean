-- Prove2me | Theorems.Thm_lean_workbook_plus_36672
-- name    : lean_workbook_plus_36672
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f4650cf3-cdf1-4a6e-abc1-c222cae55405
-- statement:
--   Denote $a+b-c=x, a-b+c=y,-a+b+c=z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36672 (a b c x y z : ℝ) (h1 : x = a + b - c) (h2 : y = a - b + c) (h3 : z = -a + b + c) : x + y + z = a + b + c   :=  by sorry
