-- Prove2me | solution 1 for BookSixth.latin_upper_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:25:02.69039+00:00
-- url     : https://prove2.me/submissions/7d64f0f2-ddb8-41e1-8050-1a45cc00c1a9

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (e : ℕ → ℝ)
    (hnn : ∀ k ∈ Finset.Icc 1 n, 0 ≤ e k)
    (hstep : ∀ k ∈ Finset.Icc 1 n,
      e k ≤ (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) :
    ∏ k ∈ Finset.Icc 1 n, e k
      ≤ ∏ k ∈ Finset.Icc 1 n,
        (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  apply Finset.prod_le_prod
  · intro k hk
    exact hnn k hk
  · intro k hk
    exact hstep k hk
