-- Prove2me | Theorems.Thm_lean_workbook_plus_44977
-- name    : lean_workbook_plus_44977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ddf88981-5e55-49e6-9279-c0fd285c1226
-- statement:
--   Prove $ \frac{27t^{4}+1}{t^{2}-2t+1} \geq 18t-3$ for $ 0<t<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44977 (t : ℝ) (ht : 0 < t ∧ t < 1) :
  (27 * t ^ 4 + 1) / (t ^ 2 - 2 * t + 1) ≥ 18 * t - 3   :=  by sorry
