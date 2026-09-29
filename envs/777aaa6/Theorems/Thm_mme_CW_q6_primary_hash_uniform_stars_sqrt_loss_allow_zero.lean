-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_allow_zero
-- name    : mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_allow_zero
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:09:14.254442+00:00
-- url     : https://prove2.me/theorems/63e2d522-3e70-4906-9ea0-d084c3516f88
-- title:
--   Uniform induced-star estimates including zero outer mass
-- statement:
--   The uniform square-root-loss primary-hash family theorem extends to nonnegative outer counts, assuming the same total-count identity and strict balance inequality. Zero outer counts use the exact single-star family; positive outer counts use the existing theorem. Both directional estimates and the four-to-the-N fiber bound are retained. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_CW_q6_zero_outer_exact_hash_family
open MME Filter

theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_allow_zero
    (L G : ℕ → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ := Nat.choose (2 * N) (L N) * Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
          H ≤ 4 ^ N ∧
          (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (middle : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
