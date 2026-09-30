-- Prove2me | solution 1 for lean_workbook_plus_75233
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:42.404524+00:00
-- url     : https://prove2.me/submissions/ac94cf4e-0a12-4bf7-a91c-88e3eeb68a42

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {a b c d : ℝ} :
    2 * (a ^ 2 - a * b + b ^ 2) * (c ^ 2 - c * d + d ^ 2) ≥
      a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by
  nlinarith [sq_nonneg ((a - b) * (c - d)), sq_nonneg (a * d - b * c)]
