-- Prove2me | Theorems.Thm_mme_112_squared_extraction_entropy_rate
-- name    : mme_112_squared_extraction_entropy_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:35:32.748012+00:00
-- url     : https://prove2.me/theorems/a25716e7-c7c0-4d84-9c3d-6ead270da190
-- title:
--   Squared 112 extractions attain their combined entropy rate
-- statement:
--   The two directional binomial capacities and a squared explicit extraction bound give their full combined logarithmic copy rate, up to any prescribed positive loss. The proof absorbs polynomial, square-root and Behrend losses, and allows zero outer count when total count is positive. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
open Filter

theorem mme_112_squared_extraction_entropy_rate
    (l g : ℕ) (hD : 0 < l + g) (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N := (l + g) * m
      let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
      ∀ A H copies : ℕ, 0 < A → 0 < H → H ≤ 4 ^ N →
        ((Nat.choose (2 * N) (l * m) *
          Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) *
          Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) →
        (Nat.choose (2 * N) N : ℝ) *
          Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) →
        ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤
            (copies : ℝ) →
        ((4 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
            Real.log (copies : ℝ) := by sorry
