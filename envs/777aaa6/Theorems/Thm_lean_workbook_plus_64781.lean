-- Prove2me | Theorems.Thm_lean_workbook_plus_64781
-- name    : lean_workbook_plus_64781
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5c12e413-932d-4bc4-a104-e325dcc602a9
-- statement:
--   Another way: Suppose $E$ is the expected time. Then $E$ is equal to $\dfrac{1}{3} \cdot 2$ (time if he picks the first opening), plus $\dfrac{1}{3} \cdot (3 + E)$ (time if he picks the second opening; the plus E is because he's at the exact same situation after he traveled 3 hours), plus $\dfrac{1}{3} \cdot (5 + E)$ (time if he picks the third opening, see above). So $E = \dfrac{2 + (3 + E) + (5 + E)}{3}$ $3E = 10 + 2E$ $E = 10$ So he will need 10 hours on average.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64781  (e : ℝ)
  (h₀ : e = (2 + (3 + e) + (5 + e)) / 3) :
  e = 10   :=  by sorry
