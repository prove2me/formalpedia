-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialU76.effective_base_seven
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:48:19.293508+00:00
-- url     : https://prove2.me/submissions/a56a1d01-411f-4305-9166-f9e65dafb48d

-- Sol generated from Novelty/ZeroFitDialU76.lean
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




lemma padicLimit_seven : padicLimit 7 = 7 / 19 := by norm_num [padicLimit]



/-- The asymptotic ceiling is strictly decreasing in the base. -/
theorem padicLimit_strict_anti {p r : ℕ} (hp : 1 ≤ p) (hpr : p < r) :
    padicLimit r < padicLimit p := by
  have hq : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hlt : (p : ℚ) < (r : ℚ) := by exact_mod_cast hpr
  have h1 : (0 : ℚ) < (p : ℚ) ^ 2 + (p : ℚ) + 1 := by nlinarith
  have h2 : (0 : ℚ) < (r : ℚ) ^ 2 + (r : ℚ) + 1 := by nlinarith
  rw [padicLimit, padicLimit, div_lt_div_iff₀ h2 h1]
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr (by nlinarith : (1 : ℚ) < (p : ℚ) * r))]



/-! ## 3. Recorded round-65 data (exp 533, seeds 20261170–72) -/







/-! ## 4. Flatness: no tie mechanism can move the dial between bitlen 72 and 76 -/



/-! ## 5. The effective base: inverting the ceiling law on the observed window -/






open Catalog.Novelty.ZeroFitDialU76 in
theorem solution:
    (seedWindowLow ≤ padicLimit 7 ∧ padicLimit 7 ≤ seedWindowHigh) ∧
    ∀ p : ℕ, 2 ≤ p → p ≠ 7 →
      ¬ (seedWindowLow ≤ padicLimit p ∧ padicLimit p ≤ seedWindowHigh) := by
  have h7 : padicLimit 7 = 7 / 19 := padicLimit_seven
  have h6 : padicLimit 6 = 18 / 43 := by norm_num [padicLimit]
  have h8 : padicLimit 8 = 24 / 73 := by norm_num [padicLimit]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h7]; norm_num [seedWindowLow, seed70]
  · rw [h7]; norm_num [seedWindowHigh, seed71]
  · intro p hp hne ⟨hlo, hhi⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- p ≤ 6 : the ceiling is at least `padicLimit 6 > 0.618²`
      have hle : padicLimit 6 ≤ padicLimit p := by
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with h | h
        · exact le_of_eq (by rw [h])
        · exact le_of_lt (padicLimit_strict_anti (by omega) h)
      have : (18 : ℚ) / 43 ≤ padicLimit p := by rw [← h6]; exact hle
      have hbad : seedWindowHigh < 18 / 43 := by norm_num [seedWindowHigh, seed71]
      linarith
    · -- p ≥ 8 : the ceiling is at most `padicLimit 8 < 0.593²`
      have hge : padicLimit p ≤ padicLimit 8 := by
        rcases eq_or_lt_of_le (show (8 : ℕ) ≤ p by omega) with h | h
        · exact le_of_eq (by rw [← h])
        · exact le_of_lt (padicLimit_strict_anti (by omega) h)
      have : padicLimit p ≤ 24 / 73 := by rw [← h8]; exact hge
      have hbad : (24 : ℚ) / 73 < seedWindowLow := by norm_num [seedWindowLow, seed70]
      linarith
