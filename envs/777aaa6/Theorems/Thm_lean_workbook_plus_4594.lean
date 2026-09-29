-- Prove2me | Theorems.Thm_lean_workbook_plus_4594
-- name    : lean_workbook_plus_4594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2fa13e03-5d26-44d6-94cb-4eed362556e0
-- statement:
--   Let $2p+1 = q$, then prove that $\frac{q-1}{2} = p$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4594 (p q : ℕ) (h₁ : 2 * p + 1 = q) : (q - 1) / 2 = p   :=  by sorry
