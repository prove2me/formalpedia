-- Prove2me | Theorems.Thm_gpy_selbergMass_le
-- name    : gpy_selbergMass_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:18:37.847491+00:00
-- url     : https://prove2.me/theorems/15fc655a-4fa4-4356-82d9-4ee3c43a1a1e
-- title:
--   Selberg mass sum bound via τ-weights
-- statement:
--   For R ≥ 2 and any k and degree, the divisor-weighted Selberg mass sum ∑_{D ≤ R} τ_{k+1}(D)·|μ(D)(1 − log D/log R)^deg| is at most R·(1 + log R)^k. Each term is at most τ_{k+1}(D), since |μ| ≤ 1 and the cutoff factor lies in [0, 1] on the range, so the bound follows from the higher divisor summatory bound.
-- source:
--   GPY τ-moment / divisor-sum estimates for Selberg weights, formalized from Mathlib (divisor double count, harmonic bound, divisor convolution, and the τ-weighted λ-mass identity)

import Mathlib
open Classical

theorem gpy_selbergMass_le {k R deg : ℕ} (hR : 2 ≤ R) :
    ∑ D ∈ Finset.Icc 1 R,
      ((((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D)).card : ℕ) : ℝ)
      * |(ArithmeticFunction.moebius D : ℝ)
        * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
      ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by sorry
