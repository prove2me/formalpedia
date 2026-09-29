-- Prove2me | Theorems.Thm_lean_workbook_plus_77958
-- name    : lean_workbook_plus_77958
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2c25cc8a-169a-458e-8c38-9f9bff24b257
-- statement:
--   $ a \;=\; \dfrac { \pi^2\cdot \pi - ( \pi^3 - 6 \pi ) } { \pi^7 \left( \dfrac {1}{3} - \dfrac {2}{5} + \dfrac {1}{7} \right) } \;=\; \boxed { \dfrac { 315 } { 4\; \pi^6 } }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77958 :
  (π^2 * π - (π^3 - 6 * π)) / (π^7 * (1 / 3 - 2 / 5 + 1 / 7)) = 315 / (4 * π^6)   :=  by sorry
