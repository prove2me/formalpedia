-- Prove2me | Theorems.Thm_lean_workbook_plus_72948
-- name    : lean_workbook_plus_72948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a8a0585c-ca2e-4d0e-9d9b-1c1bf986f486
-- statement:
--   Let $a\ge c \ge 0,b\ge d\ge0$ and $4a+3d=4b+3c$ . Prove that : $\sqrt{ab}\ge \frac{c+d}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72948 (a b c d : ℝ) (h1 : a ≥ c ∧ c ≥ 0 ∧ b ≥ d ∧ d ≥ 0) (h2 : 4 * a + 3 * d = 4 * b + 3 * c) : √(a * b) ≥ (c + d) / 2   :=  by sorry
