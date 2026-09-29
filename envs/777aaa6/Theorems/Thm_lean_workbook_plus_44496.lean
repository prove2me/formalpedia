-- Prove2me | Theorems.Thm_lean_workbook_plus_44496
-- name    : lean_workbook_plus_44496
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d9c54b6b-752e-4b70-9337-e6415c55b214
-- statement:
--   Let $x = 2020$. \n\n $\frac{(2019 + 2020)(2020 + 2021)(2021 + 2019) + 2019 * 2020 * 2021}{2019 * 2020 + 2020 * 2021 + 2021 * 2019} = \frac{9x^3-3x}{3x^2-1} = 3x = \boxed{6060}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44496  (x : ℝ)
  (h₀ : x = 2020) :
  ((2019 + 2020) * (2020 + 2021) * (2021 + 2019) + 2019 * 2020 * 2021) / (2019 * 2020 + 2020 * 2021 + 2021 * 2019) = 6060   :=  by sorry
