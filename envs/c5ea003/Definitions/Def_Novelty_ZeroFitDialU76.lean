-- Prove2me | Definitions.Def_Novelty_ZeroFitDialU76
-- name    : Novelty_ZeroFitDialU76
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:55:18.73882+00:00
-- url     : https://prove2.me/theorems/95c9f431-2a97-4729-b019-449e62ff89af
-- title:
--   Aether Catalog definitions — Novelty_ZeroFitDialU76
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ZeroFitDialU76`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ZeroFitDialU76.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64

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

namespace Catalog.Novelty.ZeroFitDialU76

open Catalog.Novelty.ZeroFitDialU64

/-! ## 1. The base-`p` tie profile -/

/-- Tie profile of the base-`p` trailing-zero statistic (the `p`-adic valuation) on
`{0,…,p^b-1}`: blocks of sizes `(p-1)p^{b-1}, …, (p-1)p, (p-1)` followed by the
singleton block `{0}`. -/
def padicBlocks (p : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | b + 1 => (p - 1) * p ^ b :: padicBlocks p b





/-! ## 2. The `p`-adic ceiling law -/


/-- The asymptotic base-`p` tie ceiling `3p/(p²+p+1)`; at `p = 2` this is `6/7`. -/
def padicLimit (p : ℕ) : ℚ := 3 * (p : ℚ) / ((p : ℚ) ^ 2 + (p : ℚ) + 1)








/-! ## 3. Recorded round-65 data (exp 533, seeds 20261170–72) -/

/-- Seed 20261170. -/
def seed70 : ℚ := 593 / 1000
/-- Seed 20261171. -/
def seed71 : ℚ := 618 / 1000
/-- Seed 20261172. -/
def seed72 : ℚ := 612 / 1000
/-- Pooled estimate at bitlen 76. -/
def pooled76 : ℚ := 608 / 1000
/-- Lower CI endpoint. -/
def ciLow76 : ℚ := 588 / 1000
/-- Upper CI endpoint. -/
def ciHigh76 : ℚ := 631 / 1000
/-- Advantage of `T` over the plain count statistic. -/
def countGap : ℚ := 73 / 1000
/-- Lower CI endpoint of the `T`-versus-count gap. -/
def gapLow : ℚ := 45 / 1000
/-- Upper CI endpoint of the `T`-versus-count gap. -/
def gapHigh : ℚ := 97 / 1000






/-! ## 4. Flatness: no tie mechanism can move the dial between bitlen 72 and 76 -/



/-! ## 5. The effective base: inverting the ceiling law on the observed window -/

/-- The observed seed window, squared: `[0.593², 0.618²]`. -/
def seedWindowLow : ℚ := seed70 ^ 2
/-- Upper end of the squared seed window. -/
def seedWindowHigh : ℚ := seed71 ^ 2




end Catalog.Novelty.ZeroFitDialU76


