-- Prove2me | Theorems.Thm_mme_rational_coarse_penalty_certificate
-- name    : mme_rational_coarse_penalty_certificate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:00:29.437977+00:00
-- url     : https://prove2.me/theorems/5ea75d75-9693-48d7-8192-db9533b8b7cf
-- title:
--   Rational certificates for coarse entropy minus penalty
-- statement:
--   A finite rational inequality involving a split probability and two positive coordinate reference probabilities certifies a real lower bound for coarse entropy minus the maximum-entropy penalty. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_entropy_dyadic_bounds
import Theorems.Thm_mme_cross_entropy_dyadic_upper
import Theorems.Thm_mme_entropy_penalty_le_pair_reference
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_rational_coarse_penalty_certificate
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℚ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin (half + 1) → ℚ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hpmass : ∑ v, p v = 1) (hqmass : ∑ v, q v = 1)
    (k0 kp kq : Fin (half + 1) → ℕ) (ka : Split half parent → ℕ) (b : ℚ) :
    let m := fun i v => ∑ c : {c : Split half parent // c.val i = v}, alpha c.val
    b ≤
      (∑ v, m 0 v * ((k0 v : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ k0 v * m 0 v)) +
      (∑ c, alpha c * ((ka c : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ ka c * alpha c)) -
      (∑ v, m i v * ((kp v : ℚ) * (693147181 / 1000000000) - 1 +
        (2 ^ kp v * p v)⁻¹)) -
      (∑ v, m j v * ((kq v : ℚ) * (693147181 / 1000000000) - 1 +
        (2 ^ kq v * q v)⁻¹)) →
    (b : ℝ) ≤
      entropy (mme_modern_marginal (fun c : Split half parent => c.val 0)
        (fun c => (alpha c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alpha c : ℝ)) := by sorry
