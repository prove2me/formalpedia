-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialU76.padic_spearmanSq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:50:41.988657+00:00
-- url     : https://prove2.me/submissions/c4951046-fdd8-4836-b49c-86b012aed976

-- Sol generated from Novelty/ZeroFitDialU76.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_spearmanSq_eq
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_tieCorr_cons
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU76_ceiling_algebra
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU76_padicBlocks_sum

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




/-- Cast of one block size. -/
lemma cast_block (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    (((p - 1) * p ^ k : ℕ) : ℚ) = ((p : ℚ) - 1) * (p : ℚ) ^ k := by
  push_cast [Nat.cast_sub hp]
  ring

/-- **Closed form for the tie correction of the `p`-adic profile.** -/
lemma tieCorr_padic (p : ℕ) (hp : 1 ≤ p) (b : ℕ) :
    12 * ((p : ℚ) ^ 3 - 1) * tieCorr (padicBlocks p b)
      = ((p : ℚ) - 1) ^ 3 * (((p : ℚ) ^ b) ^ 3 - 1)
        - ((p : ℚ) ^ 3 - 1) * ((p : ℚ) ^ b - 1) := by
  induction b with
  | zero => norm_num [padicBlocks, tieCorr]
  | succ k ih =>
      rw [padicBlocks, tieCorr_cons, cast_block p hp k]
      have hstep : ((p : ℚ) ^ (k + 1)) = (p : ℚ) * (p : ℚ) ^ k := by ring
      rw [hstep]
      set q : ℚ := (p : ℚ)
      set Y : ℚ := q ^ k
      nlinarith [ih, sq_nonneg q, sq_nonneg Y]

/-! ## 2. The `p`-adic ceiling law -/










/-! ## 3. Recorded round-65 data (exp 533, seeds 20261170–72) -/







/-! ## 4. Flatness: no tie mechanism can move the dial between bitlen 72 and 76 -/



/-! ## 5. The effective base: inverting the ceiling law on the observed window -/






open Catalog.Novelty.ZeroFitDialU76 in
theorem solution(p b : ℕ) (hp : 2 ≤ p) (hb : 1 ≤ b) :
    spearmanSq (padicBlocks p b)
      = padicLimit p * (1 + 1 / ((p : ℚ) ^ b * ((p : ℚ) ^ b + 1))) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hsum : (padicBlocks p b).sum = p ^ b := padicBlocks_sum p hp1 b
  have hq : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hY : (2 : ℚ) ≤ (p : ℚ) ^ b := by
    calc (2 : ℚ) = (2 : ℚ) ^ 1 := (pow_one 2).symm
      _ ≤ (p : ℚ) ^ 1 := by gcongr
      _ ≤ (p : ℚ) ^ b := by
          apply pow_le_pow_right₀ (by linarith) hb
  have h2 : 2 ≤ (padicBlocks p b).sum := by
    rw [hsum]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      _ ≤ p ^ b := Nat.pow_le_pow_left hp b
  have hcast : (((padicBlocks p b).sum : ℕ) : ℚ) = (p : ℚ) ^ b := by
    rw [hsum]; push_cast; ring
  rw [spearmanSq_eq _ h2, hcast, padicLimit]
  set q : ℚ := (p : ℚ) with hqdef
  set Y : ℚ := q ^ b with hYdef
  have hqqpos : (0 : ℚ) < q ^ 2 + q + 1 := by nlinarith
  have hq3pos : (0 : ℚ) < q ^ 3 - 1 := by
    have hfac : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    rw [hfac]
    exact mul_pos (by linarith) hqqpos
  have hq3 : q ^ 3 - 1 ≠ 0 := ne_of_gt hq3pos
  have hqq : q ^ 2 + q + 1 ≠ 0 := ne_of_gt hqqpos
  have hY0 : Y ≠ 0 := ne_of_gt (by linarith)
  have hY1 : Y + 1 ≠ 0 := ne_of_gt (by linarith)
  have hYm : Y - 1 ≠ 0 := ne_of_gt (by linarith)
  have hcube : Y ^ 3 - Y ≠ 0 := by
    have : Y ^ 3 - Y = Y * (Y - 1) * (Y + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hY0 hYm) hY1
  have key : 12 * tieCorr (padicBlocks p b)
      = ((q - 1) ^ 3 * (Y ^ 3 - 1) - (q ^ 3 - 1) * (Y - 1)) / (q ^ 3 - 1) := by
    have hpad := tieCorr_padic p hp1 b
    rw [eq_div_iff hq3]
    linear_combination hpad
  rw [key]
  exact ceiling_algebra q Y hq hY
