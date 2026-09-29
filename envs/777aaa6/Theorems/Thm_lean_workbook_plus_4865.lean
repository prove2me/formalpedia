-- Prove2me | Theorems.Thm_lean_workbook_plus_4865
-- name    : lean_workbook_plus_4865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7a659666-a5e5-44d6-a993-81f38530abea
-- statement:
--   Thus, we have $\frac{\frac{5w}{8}+\frac{5w}{12}+\frac{5w}{16}}{w}=\frac{65}{48}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4865  (w : ℝ)
  (h₀ : w ≠ 0) :
  ((5 * w / 8 + 5 * w / 12 + 5 * w / 16) / w) = 65 / 48   :=  by sorry
