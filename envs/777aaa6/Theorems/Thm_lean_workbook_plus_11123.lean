-- Prove2me | Theorems.Thm_lean_workbook_plus_11123
-- name    : lean_workbook_plus_11123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c8ed9a2f-ca62-4526-a913-036f189e7676
-- statement:
--   Consider the equation modulo 4. We have $x^{2}\equiv-y\pmod{4}$ . Since $x^2$ can be congruent to only 0 or 1 mod 4, $y$ is congruent to 0 or -1 mod 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11123 : ∀ x y : ℤ, (x^2 ≡ -y [ZMOD 4]) → (y ≡ 0 [ZMOD 4]) ∨ (y ≡ -1 [ZMOD 4])   :=  by sorry
