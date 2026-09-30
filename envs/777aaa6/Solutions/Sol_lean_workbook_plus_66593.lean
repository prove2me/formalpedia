-- Prove2me | solution 1 for lean_workbook_plus_66593
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:41.785003+00:00
-- url     : https://prove2.me/submissions/44335d64-5bac-4151-9885-67e924814577

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha1 : 1 ≥ a ∧ a ≥ 1/5) : 32*a^5 + 32*a^4 - 16*a^3 - 16*a^2 + 9*a - 1 ≥ 0 := by
  obtain ⟨h1, h2⟩ := ha1
  have hb : 0 ≤ 1 - a := by linarith
  have hc : 0 ≤ a - 1/5 := by linarith
  nlinarith [mul_nonneg hb hc, mul_nonneg (mul_nonneg hb hc) hc, mul_nonneg (mul_nonneg hb hc) hb,
    sq_nonneg (a - 1/2), mul_nonneg hc (sq_nonneg (a - 1/2)), mul_nonneg hb (sq_nonneg (a - 1/2)),
    mul_nonneg (mul_nonneg hb hc) (sq_nonneg (a - 1/2)), mul_nonneg hc (sq_nonneg a),
    mul_nonneg (mul_nonneg hc hc) (sq_nonneg a), pow_nonneg hc 3, pow_nonneg hc 4, pow_nonneg hc 5]
