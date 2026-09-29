-- Prove2me | solution 1 for lean_workbook_plus_41117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:12.330264+00:00
-- url     : https://prove2.me/submissions/97a08a6d-8ab0-4bcc-b969-e0d1e972ea9d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (m n : ℤ) : (2*m+1)^2 - (2*n+1)^2 ≡ 0 [ZMOD 8] := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self m
  obtain ⟨l, hl⟩ := Int.even_mul_succ_self n
  apply Int.modEq_zero_iff_dvd.mpr
  refine ⟨k - l, ?_⟩
  nlinarith [hk, hl]
