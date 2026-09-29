-- Prove2me | Theorems.Thm_mme_nat_div_real_half_lower
-- name    : mme_nat_div_real_half_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:08:21.415505+00:00
-- url     : https://prove2.me/theorems/0cd19cbf-17d9-4d03-9676-65ddd6e2d335
-- title:
--   A nonzero natural quotient retains half its real value
-- statement:
--   For positive integers $d\le n$, integer division loses at most a factor two compared with real division:
--
--   $$
--   \frac{n}{2d}\le \left\lfloor\frac nd\right\rfloor.
--   $$
--
--   Indeed the quotient is at least one, while the remainder is smaller than $d$. This elementary estimate absorbs the final floor in finite hash-family cardinality bounds.
-- source:
--   Elementary Euclidean-division estimate used to absorb integer rounding in finite combinatorial extraction bounds.

import Mathlib

theorem mme_nat_div_real_half_lower
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (n : ℝ) / (2 * (d : ℝ)) ≤ ((n / d : ℕ) : ℝ) := by
  sorry
