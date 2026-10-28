-- Prove2me | Theorems.Thm_gpy_lambdaMass_selberg
-- name    : gpy_lambdaMass_selberg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:04:05.288314+00:00
-- url     : https://prove2.me/theorems/3b6a9d0c-9326-4ebe-8977-45bacb337319
-- title:
--   Selberg weights: exact τ-weighted λ-mass identity
-- statement:
--   Let k be a tuple length, R a level, and deg a degree. Let the Selberg weight be lam_d = mu(prod d) * (1 - log(prod d)/log R)^deg when prod d <= R, and 0 otherwise, and let tupleProdCount k D be the number of ordered factorizations of D into k positive factors (the k-fold divisor function tau_k(D)). Then the lambda-mass sum_{d, e in support} |lam_d * lam_e| equals the square of the divisor-weighted sum sum_{D in [1, R]} tau_k(D) * |mu(D) * (1 - log D/log R)^deg|. This is the exact tau-weighted mass identity: the squarefree restriction (via mu) and the polynomial decay (via the cutoff factor) stay visible, instead of being thrown away into a crude support-size bound.
-- source:
--   GPY Selberg weights: the exact tau-weighted lambda-mass identity, from the fiberwise identity over support fibers

import Mathlib
open Classical

theorem gpy_lambdaMass_selberg {k R deg : ℕ} :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        |(if ∏ i, d i ≤ R then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
              * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0)
        * (if ∏ i, e i ≤ R then
            (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
              * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0)|)
      = (∑ D ∈ Finset.Icc 1 R,
          (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
            (fun d => ∏ i, d i = D)).card : ℝ)
            * |(ArithmeticFunction.moebius D : ℝ)
              * (1 - Real.log D / Real.log R) ^ deg|) ^ 2 := by sorry
