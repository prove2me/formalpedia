-- Prove2me | solution 1 for lean_workbook_plus_77555
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:26.979617+00:00
-- url     : https://prove2.me/submissions/341b4666-8ac0-41b9-8d1b-6b44ae6be9fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {p q r : ℝ} (hp : p > 0 ∧ q > 0 ∧ r > 0) (hpq : p + q + r = 1) (hpqr : p * q * r = 1) : 12 * p * q * r ≥ 2 * (4 * q - p ^ 2) * (p ^ 2 - q) := by
  (intros; nlinarith)
