-- Prove2me | solution 1 for lean_workbook_plus_14704
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:48.820726+00:00
-- url     : https://prove2.me/submissions/d97dee45-ee5b-4cd8-a22c-e025be5ff1a6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ {a b c d : ℤ} {p : ℕ} {k : ℕ},
  a + d - b - c ≡ 0 [ZMOD p ^ k] → a ≡ b + c - d [ZMOD p ^ k] := by
  intro a b c d p k h
  apply Int.modEq_iff_dvd.mpr
  have hh := Int.modEq_iff_dvd.mp h
  convert hh using 1 <;> ring
