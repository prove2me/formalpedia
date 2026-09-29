-- Prove2me | Theorems.Thm_lean_workbook_plus_11949
-- name    : lean_workbook_plus_11949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e6cfbca3-bb4a-4e58-b4a1-787002d3dbd9
-- statement:
--   Now, since $ b,c \ge 0$ , using AM-GM, we get $ \frac {b + c}{2} \ge \sqrt {bc} \rightarrow (b + c)^2 \ge 4bc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11949 :
  ∀ b c : ℝ, b ≥ 0 ∧ c ≥ 0 → (b + c)^2 ≥ 4 * b * c   :=  by sorry
