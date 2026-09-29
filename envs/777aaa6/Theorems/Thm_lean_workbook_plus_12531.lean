-- Prove2me | Theorems.Thm_lean_workbook_plus_12531
-- name    : lean_workbook_plus_12531
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/28820bd9-4158-4605-bd93-3aac44953ab6
-- statement:
--   If $p - a^2 | p - b^2$, show that $p - a^2 | (a + b)(a - b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12531 (p a b : ℤ) (h : p - a^2 ∣ p - b^2) :
  p - a^2 ∣ (a + b) * (a - b)   :=  by sorry
