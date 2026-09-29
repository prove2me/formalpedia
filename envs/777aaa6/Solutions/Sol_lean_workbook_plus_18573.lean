-- Prove2me | solution 1 for lean_workbook_plus_18573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:35.976011+00:00
-- url     : https://prove2.me/submissions/981a16ce-9418-4897-894b-12fc70e053ed

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {p q r : ℝ} : p * q + q * r + r * p ≤ p ^ 2 + q ^ 2 + r ^ 2 := by
  intros
  nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg r, sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r)]
