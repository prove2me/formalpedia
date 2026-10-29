-- Prove2me | Theorems.Thm_gpy_lambdaMass_at_lcm_le
-- name    : gpy_lambdaMass_at_lcm_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T21:47:55.369055+00:00
-- url     : https://prove2.me/theorems/9f54be21-924d-4c40-beec-01683e35f710
-- title:
--   Minimal weights: per-modulus τ mass bound
-- statement:
--   For level R ≥ 2, exponent kk, and any combined-modulus tuple L, consider the minimal tuple weights λ_d = (∏ᵢ μ(dᵢ)) · (1 − log(∏ᵢ dᵢ)/log R)^kk, truncated to zero when ∏ᵢ dᵢ > R, over support pairs (d, e) of tuples with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. The λ-mass at fixed combined modulus — the sum of |λ_d λ_e| over support pairs whose coordinatewise lcm equals L — is at most ∏ⱼ τ(Lⱼ)², the product over coordinates of the squared divisor counts, since |λ| ≤ 1 on the support and each coordinate pair lies in the divisors of Lⱼ. This is a foundation ingredient for a sharp argument, not a separation claim: it does not by itself close the GPY argument, which still needs the weighted BV combination and a main-term lower bound.
-- source:
--   GPY minimal polynomial-truncated lambda weights: per-modulus tau-weighted mass bound, from |lambda| <= 1 on the support and the divisor count of lcm pairs

import Mathlib
open Classical

theorem gpy_lambdaMass_at_lcm_le {k R kk : ℕ} (hR : 2 ≤ R) (L : Fin k → ℕ) :
    (∑ p ∈ (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)) ×ˢ
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R))).filter
      (fun p => ∀ j, Nat.lcm (p.1 j) (p.2 j) = L j),
      abs (((∏ i, ((ArithmeticFunction.moebius (p.1 i) : ℤ) : ℝ)) *
          (if ∏ i, p.1 i ≤ R then
            (1 - Real.log ((∏ i, p.1 i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
          else 0))
        * ((∏ i, ((ArithmeticFunction.moebius (p.2 i) : ℤ) : ℝ)) *
          (if ∏ i, p.2 i ≤ R then
            (1 - Real.log ((∏ i, p.2 i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
          else 0))))
      ≤ ((∏ j, (Nat.divisors (L j)).card ^ 2 : ℕ) : ℝ) := by sorry
