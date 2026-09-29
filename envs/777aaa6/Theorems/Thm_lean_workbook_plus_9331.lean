-- Prove2me | Theorems.Thm_lean_workbook_plus_9331
-- name    : lean_workbook_plus_9331
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a3151eb0-c2c6-44e9-9b3e-0376b45f9cba
-- statement:
--   Evaluate $A = \dfrac{2020}{1+\dfrac{2017}{2018} + \dfrac{2017}{2019}} + \dfrac{2020} {1+\dfrac{2018}{2017} + \dfrac{2018}{2019}} \ + \dfrac{2020}{1+\dfrac{2019}{2017} + \dfrac{2019}{2018}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9331 (A : ℝ) : A = 2020 / (1 + 2017 / 2018 + 2017 / 2019) + 2020 / (1 + 2018 / 2017 + 2018 / 2019) + 2020 / (1 + 2019 / 2017 + 2019 / 2018) → A = 2020   :=  by sorry
