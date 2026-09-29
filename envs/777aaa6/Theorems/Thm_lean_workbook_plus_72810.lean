-- Prove2me | Theorems.Thm_lean_workbook_plus_72810
-- name    : lean_workbook_plus_72810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4e45837d-df95-4cec-9c2a-ca01312c53c9
-- statement:
--   Since $u + v + w = 1$, we have $(uv + vw + wu) \leq \frac{1}{3}$. Also, by AM - GM, we have $uvw \geq \frac{1}{27}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72810  (u v w : ℝ)
  (h₀ : u + v + w = 1) :
  u * v + v * w + w * u ≤ 1 / 3   :=  by sorry
