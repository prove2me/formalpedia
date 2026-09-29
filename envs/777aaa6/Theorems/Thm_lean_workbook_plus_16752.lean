-- Prove2me | Theorems.Thm_lean_workbook_plus_16752
-- name    : lean_workbook_plus_16752
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6b2619be-619f-4afd-88b9-888a20047b65
-- statement:
--   If $ \sqrt {x^2 + y^2 + z^2} < \varepsilon$ then $ |x| < \varepsilon$ , $ |y| < \varepsilon$ and $ |z| < \varepsilon$ . Therefore ....
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16752 (x y z ε : ℝ) (h : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) < ε) :
  |x| < ε ∧ |y| < ε ∧ |z| < ε   :=  by sorry
