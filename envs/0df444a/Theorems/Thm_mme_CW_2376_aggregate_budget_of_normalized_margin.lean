-- Prove2me | Theorems.Thm_mme_CW_2376_aggregate_budget_of_normalized_margin
-- name    : mme_CW_2376_aggregate_budget_of_normalized_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:37:59.302061+00:00
-- url     : https://prove2.me/theorems/4bf17346-3714-4d48-a494-e42c93b55dc0
-- title:
--   The normalized CW hash margin lifts to the full aggregate budget
-- statement:
--   Let $N\ge1$. Suppose the number of target edges factors as $T=VD_*$, where $V$ is the number of vertices in one mode and $D_*$ is the target-profile completion degree. If
--
--   $$
--   p^2\ell+3D_*D\le D_*|S|,
--   $$
--
--   then
--
--   $$
--   p^{N+1}V\ell+3TDp^{N-1}\le T|S|p^{N-1}.
--   $$
--
--   The factors $p^{N+1}$ and $p^{N-1}$ are respectively the number of affine hash states and the common fiber factor in the target-survival and collision sums. This lemma restores those common factors after the prime/Behrend collision estimate has been normalized.
-- source:
--   Algebraic normalization of the affine-hash counting argument in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

theorem mme_CW_2376_aggregate_budget_of_normalized_margin
    (N p T S D Dstar : ℕ) (V loss : ℝ)
    (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hT : (T : ℝ) = V * (Dstar : ℝ))
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S : ℝ)) :
    (p : ℝ) ^ (N + 1) * (V * loss) +
        3 * (T : ℝ) * (D : ℝ) * (p : ℝ) ^ (N - 1) ≤
      (T : ℝ) * (S : ℝ) * (p : ℝ) ^ (N - 1) := by
  sorry
