-- Prove2me | Theorems.Thm_mme_le_of_frequently_pow_half_le
-- name    : mme_le_of_frequently_pow_half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:19:07.345253+00:00
-- url     : https://prove2.me/theorems/2544f640-9371-4e3f-a8ec-20b0ef026cc6
-- title:
--   A frequent exponential comparison determines the base
-- statement:
--   Let $V\ge1$ and $R\ge0$. Suppose that for arbitrarily large natural numbers $N$ one has
--
--   $$
--   \frac12 V^N\le R^N.
--   $$
--
--   Then $V\le R$. The fixed factor $1/2$ is subexponential and therefore cannot compensate for a strictly larger exponential base. This is the final real-analysis step in the unrestricted tau-value versus asymptotic-rank bridge.
-- source:
--   Standard consequence of convergence of geometric powers with ratio in [0,1); formalized using Mathlib's tendsto_pow_atTop_nhds_zero_of_lt_one.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
open Filter

theorem mme_le_of_frequently_pow_half_le {V R : ℝ}
    (hV : 1 ≤ V) (hR : 0 ≤ R)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      V ^ N * (1 / 2 : ℝ) ≤ R ^ N) :
    V ≤ R := by sorry
