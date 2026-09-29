-- Prove2me | Theorems.Thm_lean_workbook_plus_49294
-- name    : lean_workbook_plus_49294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9f470f4b-0c11-409d-99c6-db2d09ded33b
-- statement:
--   Let $a\ge c \ge 0,b\ge d\ge0$ and $2a+d=2b+c$ . Prove that : $2ab\ge c^2+d^2.$ (Zhangyanzong)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49294 (a b c d : ℝ) (h1 : a ≥ c ∧ c ≥ 0 ∧ b ≥ d ∧ d ≥ 0) (h2 : 2 * a + d = 2 * b + c) : 2 * a * b ≥ c ^ 2 + d ^ 2   :=  by sorry
