-- Prove2me | Theorems.Thm_lean_workbook_plus_3062
-- name    : lean_workbook_plus_3062
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5c470f62-fd2f-4a9d-8260-7abb51bd0906
-- statement:
--   Setting $ p = a + b + c \ge 3$ , then the above inequality becomes \n$ 2\left( \frac {4}{5} - \frac {3(p^2 - 6)}{5p^2}\right) \ge 3 - \frac {3p}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3062 {p : ℝ} (hp : p ≥ 3) : 2 * (4 / 5 - 3 * (p ^ 2 - 6) / (5 * p ^ 2)) ≥ 3 - 3 * p / 5   :=  by sorry
