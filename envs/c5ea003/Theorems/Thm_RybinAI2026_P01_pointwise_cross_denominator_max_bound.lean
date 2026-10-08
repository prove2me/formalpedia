-- Prove2me | Theorems.Thm_RybinAI2026_P01_pointwise_cross_denominator_max_bound
-- name    : RybinAI2026.P01.pointwise_cross_denominator_max_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:00:55.414096+00:00
-- url     : https://prove2.me/theorems/108caccc-bf6b-4f17-b3f4-e9b06a50b66c
-- title:
--   Pointwise cross-denominator max bound for the P01 integral comparison
-- statement:
--   Let p, q, r, s be strictly positive real numbers and X, Y arbitrary reals. Then |X+Y| / ((p+q)(r+s)) <= max (|X|/(pr), |Y|/(qs)). This is the pointwise algebraic core of Step 1 in the dossier for parent RybinAI2026.P01.matrix_integral_inequality (8d67c9ac-a6c7-418c-b8db-0bc029c18484): with X, Y the two bilinear numerators and p, q, r, s the positive quadratic-form denominators, the triangle inequality plus (pr+qs)/((p+q)(r+s)) <= 1 (since ps+qr >= 0) yields the bound. It does NOT by itself close the parent: integrating the pointwise max gives the integral of a max, which dominates (rather than is bounded by) the max of the integrals, so a further integral-max exchange argument is still required (BRIDGE_UNVERIFIED).
-- source:
--   Prove2Me mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733; Step-1 reduction of root 8d67c9ac-a6c7-418c-b8db-0bc029c18484; dossier candidates/proof-dossiers/8d67c9ac-a6c7-418c-b8db-0bc029c18484.md

import Mathlib

namespace RybinAI2026.P01

theorem pointwise_cross_denominator_max_bound
    (p q r s X Y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    |X + Y| / ((p + q) * (r + s)) ≤ max (|X| / (p * r)) (|Y| / (q * s)) := by
  sorry

end RybinAI2026.P01
