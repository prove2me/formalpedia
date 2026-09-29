-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialU76_effective_base_seven
-- name    : Catalog.Novelty.ZeroFitDialU76.effective_base_seven
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:20:27.069592+00:00
-- url     : https://prove2.me/theorems/33e686b0-ed68-44a2-8187-8fbfd49cee26
-- title:
--   Effective-base inversion.
-- statement:
--   **Effective-base inversion.**  Base `7` is the *unique* base whose asymptotic
--   tie ceiling `3p/(p²+p+1)` lies inside the squared seed window `[0.593², 0.618²]`
--   recorded at bitlen 76.  The observed attenuation is therefore exactly what a
--   *7-adic* — not a 2-adic — valuation profile would produce.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialU76.effective_base_seven:
--       (seedWindowLow ≤ padicLimit 7 ∧ padicLimit 7 ≤ seedWindowHigh) ∧
--       ∀ p : ℕ, 2 ≤ p → p ≠ 7 →
--         ¬ (seedWindowLow ≤ padicLimit p ∧ padicLimit p ≤ seedWindowHigh) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialU76.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialU76.lean#L313

-- Thm stub generated from Novelty/ZeroFitDialU76.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76

/-!
# The zero-fit dial at bitlen 76: the `p`-adic ceiling law and the effective base

## Research context (FACT round-65 #1, exp 533, `U76-DIAL-CONFIRMED`)

The measurement under study reports a Spearman rank correlation between a
*zero-count statistic* `T` (the number of trailing zeros of a uniformly drawn
integer) and a downstream `rate`, on uniform draws at bitlen 76:

* seeds 20261170/71/72 give `0.593 / 0.618 / 0.612`;
* pooled `0.608`, CI `[0.588, 0.631]`, all inside the validation band `[0.55, 0.85]`;
* `T` beats a plain count statistic by `+0.073`, CI `[0.045, 0.097]`;
* the dial is reported *flat within noise* from bitlen 72 to bitlen 76.

`Novelty.ZeroFitDialU64` proved the tie-attenuation law
`ρ² = 1 - 12·Σⱼ(mⱼ³-mⱼ)/(n³-n)` and evaluated it for the *dyadic* profile.
This file supplies the two pieces of mathematics that the round-65 report needs
and that the earlier files do not contain.

## Main results

* `padicBlocks`, `padicBlocks_sum` — the tie profile of the base-`p` trailing-zero
  statistic on `{0,…,p^b-1}`: blocks `(p-1)p^{b-1}, …, (p-1)p, (p-1)` and the
  singleton `{0}`.
* `tieCorr_padic` — closed form for the Kendall tie correction of that profile.
* `padic_spearmanSq` — the **`p`-adic ceiling law**
  `ρ²(p,b) = (3p/(p²+p+1)) · (1 + 1/(p^b(p^b+1)))`,
  which specialises at `p = 2` to the dyadic value `(6/7)(1+1/(2^b(2^b+1)))`
  (`padicBlocks_two`, `padic_two_eq_dyadic`).
* `padicLimit_strict_anti`, `padic_ceiling_gt_limit`, `padic_ceiling_close` — the
  base-`p` ceiling `3p/(p²+p+1)` is strictly decreasing in `p`, and the finite-`b`
  ceiling approaches it from above at rate `p^{-2b}`.
* `dial_flat_72_76` — the **flatness theorem**: the dyadic ceiling changes by less
  than `10^{-43}` between bitlen 72 and bitlen 76, so no tie mechanism can produce
  *any* bitlen dependence in that range.
* `tie_mechanism_excluded_64_76` — the recorded drop `0.648 → 0.608` exceeds the
  entire ceiling change from bitlen 64 to bitlen 76 by a factor `> 10^{30}`.
* `effective_base_seven` — the **effective-base inversion**: `p = 7` is the *unique*
  base whose asymptotic ceiling `3p/(p²+p+1)` lies inside the square of the observed
  seed range `[0.593, 0.618]`; and the finite ceiling at bitlen 76 also lies there
  (`padic_seven_76_in_seed_window`).
* Recorded-data theorems `u76_inside_band`, `u76_pooled_near_seed_mean`,
  `u76_below_tie_ceiling`, `u76_count_gap_positive`.
-/

open Finset

open Catalog.Novelty.ZeroFitDialU76

open Catalog.Novelty.ZeroFitDialU64

/-! ## 1. The base-`p` tie profile -/






/-! ## 2. The `p`-adic ceiling law -/










/-! ## 3. Recorded round-65 data (exp 533, seeds 20261170–72) -/







/-! ## 4. Flatness: no tie mechanism can move the dial between bitlen 72 and 76 -/



/-! ## 5. The effective base: inverting the ceiling law on the observed window -/

theorem Catalog.Novelty.ZeroFitDialU76.effective_base_seven:
    (seedWindowLow ≤ padicLimit 7 ∧ padicLimit 7 ≤ seedWindowHigh) ∧
    ∀ p : ℕ, 2 ≤ p → p ≠ 7 →
      ¬ (seedWindowLow ≤ padicLimit p ∧ padicLimit p ≤ seedWindowHigh) := by sorry
