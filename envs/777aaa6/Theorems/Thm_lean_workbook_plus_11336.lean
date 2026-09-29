-- Prove2me | Theorems.Thm_lean_workbook_plus_11336
-- name    : lean_workbook_plus_11336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/84e2266a-18cc-4094-ac12-9d2645623a75
-- statement:
--   So $2P + \frac{3}{8} \geq \frac{3}{4}$ . Therefore, $P \geq \frac{3}{16}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11336  (p : ℝ)
  (h₀ : 2 * p + 3 / 8 ≥ 3 / 4) :
  3 / 16 ≤ p   :=  by sorry
