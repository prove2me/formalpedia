-- Prove2me | Theorems.Thm_lean_workbook_plus_82206
-- name    : lean_workbook_plus_82206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d9cc610d-2e54-4ecd-9246-a569ef46eac4
-- statement:
--   $n=2$ . We have $x_{1}^{2}+x_{2}^{2}=1$ . Observe the fact that $(x_{1}+x_{2})^{2}\leq 2(x_{1}^{2}+x_{2}^{2})$ .It follows $x_{1}+x_{2}\leq \sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82206  (x y : ℝ)
  (h₀ : x^2 + y^2 = 1) :
  (x + y)^2 ≤ 2 * (x^2 + y^2)   :=  by sorry
