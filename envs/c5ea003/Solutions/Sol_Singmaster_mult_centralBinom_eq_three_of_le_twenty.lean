-- Prove2me | solution 1 for Singmaster.mult_centralBinom_eq_three_of_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:42:47.263827+00:00
-- url     : https://prove2.me/submissions/96af181b-a617-4582-a715-c9888efa9bb3

-- Sol generated from Combinatorics/SingmasterCentralBinomialExtended.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_choose_eq_iff_descFactorial
import Theorems.Thm_Singmaster_mult_centralBinom_eq_three_cubic
import Theorems.Thm_Singmaster_mult_centralBinom_eq_three_of_le_ten
/-
# A cubic search window: `N(C(2m,m)) = 3` up to `m = 20`, and no fives or sevens below
# `538257874440`

Sixth research cycle.  `Combinatorics.SingmasterCentralBinomial` reduced the open
question *"does any number occur exactly five or exactly seven times?"* to the single
sequence of central binomial coefficients and made the reduction effective: for
`t = C(2m,m)` the multiplicity is `3` as soon as no interior entry `C(n,k) = t` occurs
in a row `2m < n < N` with `N ≈ √(2t)` and `2 ≤ k ≤ n/2`.  Executing that quadratic
search cost `(N - 2m) · (N/2)` kernel tests and stopped at `m = 10`.

This file removes both factors of the search box.

## Two structural reductions

* **The column collapse** (`Singmaster.column_lt_of_choose_eq_centralBinom`).  In the
  escape window the column index is *tiny*: if `2k ≤ n`, `n > 2m` and
  `C(n,k) = C(2m,m)`, then `k < m`.  Indeed `C(2k,k) ≤ C(n,k)` (monotonicity in the
  row) and `m ↦ C(2m,m)` is strictly increasing, so `k ≥ m` would force
  `C(2m,m) ≤ C(2k,k) ≤ C(n,k) = C(2m,m)` with a strict inequality somewhere (from
  `k > m`, or from `n > 2m` when `k = m`).  So the columns run over `[3, m-1]`, a strip
  of height `m`, instead of a triangle of height `N/2`.

* **The triangular obstruction** (`Singmaster.choose_two_ne_of_not_sq`).  The column
  `k = 2` is the one that forces the large window `N ≈ √(2t)`, and it need not be
  searched at all: `C(n,2) = t` happens iff `t` is a triangular number, i.e. iff
  `8t + 1` is a perfect square.  A single square test therefore eliminates the whole
  column `k = 2`, after which every remaining entry satisfies `C(n,3) ≤ t` and the row
  window shrinks from `√(2t)` to `(6t)^{1/3}`.

For `m = 20` the box shrinks from `524248 × 262124` to `9347 × 17`: a saving of more
than nine orders of magnitude, which is what makes the kernel verification of
`m = 11, …, 20` possible.

## Results

* `Singmaster.two_mul_choose_two`, `Singmaster.choose_two_ne_of_not_sq` — the
  triangular obstruction;
* `Singmaster.column_lt_of_choose_eq_centralBinom` — the column collapse;
* `Singmaster.mult_centralBinom_eq_three_cubic` — the resulting criterion;
* `Singmaster.mult_centralBinom_eq_three_of_le_twenty` — `N(C(2m,m)) = 3` for every
  `2 ≤ m ≤ 20`, i.e. up to `C(40,20) = 137846528820`;
* `Singmaster.mult_ne_five_or_seven_of_lt_large` — **unconditionally, no `t` with
  `2 ≤ t < 538257874440 = C(42,21)` occurs exactly five or exactly seven times**,
  extending the previous range `705432` by a factor of more than `700000`.
-/

open Finset

open Singmaster

/-! ## The triangular obstruction: the column `k = 2` -/



/-! ## The column collapse -/


/-! ## Comparison lemmas for the truncated box -/


/-- A cheap sufficient condition for `t < C(N,k)`, phrased through the descending
factorial so that the kernel can check it with `k` multiplications. -/
theorem lt_choose_of_descFactorial {N k t : ℕ}
    (h : Nat.factorial k * t < N.descFactorial k) : t < N.choose k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  exact lt_of_mul_lt_mul_left h (Nat.zero_le _)

/-! ## The criterion -/


/-- Splitting a bounded search into two consecutive windows; used to keep the individual
kernel computations of manageable size. -/
theorem forall_Ico_glue {a b c : ℕ} {P : ℕ → Prop} (h1 : ∀ n ∈ Finset.Ico a b, P n)
    (h2 : ∀ n ∈ Finset.Ico b c, P n) : ∀ n ∈ Finset.Ico a c, P n := by
  intro n hn
  rw [Finset.mem_Ico] at hn
  rcases Nat.lt_or_ge n b with h | h
  · exact h1 n (by rw [Finset.mem_Ico]; omega)
  · exact h2 n (by rw [Finset.mem_Ico]; omega)


/-! ## Executing the criterion for `11 ≤ m ≤ 20`

Each search runs over the rectangle `2m < n < (6t)^{1/3}`, `3 ≤ k ≤ m - 1`; the largest
is `40 < n < 9388`, `3 ≤ k ≤ 19` for `m = 20`.  Every step is a kernel computation:
`decide +kernel` type-checks the Boolean evaluation in the kernel, it is *not*
`native_decide`. -/

set_option maxRecDepth 10000 in
/-- `C(22,11) = 705432` occurs exactly three times. -/
theorem mult_centralBinom_eleven : mult 705432 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 11) (s := 2375) (N := 163) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 20000 in
/-- `C(24,12) = 2704156` occurs exactly three times. -/
theorem mult_centralBinom_twelve : mult 2704156 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 12) (s := 4651) (N := 255) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 40000 in
/-- `C(26,13) = 10400600` occurs exactly three times. -/
theorem mult_centralBinom_thirteen : mult 10400600 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 13) (s := 9121) (N := 398) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 40000 in
/-- `C(28,14) = 40116600` occurs exactly three times. -/
theorem mult_centralBinom_fourteen : mult 40116600 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 14) (s := 17914) (N := 624) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 80000 in
/-- `C(30,15) = 155117520` occurs exactly three times. -/
theorem mult_centralBinom_fifteen : mult 155117520 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 15) (s := 35226) (N := 978) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 200000 in
/-- `C(32,16) = 601080390` occurs exactly three times. -/
theorem mult_centralBinom_sixteen : mult 601080390 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 16) (s := 69344) (N := 1535) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 400000 in
/-- `C(34,17) = 2333606220` occurs exactly three times. -/
theorem mult_centralBinom_seventeen : mult 2333606220 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 17) (s := 136633) (N := 2412) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 800000 in
/-- `C(36,18) = 9075135300` occurs exactly three times. -/
theorem mult_centralBinom_eighteen : mult 9075135300 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 18) (s := 269445) (N := 3792) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 2000000 in
/-- `C(38,19) = 35345263800` occurs exactly three times. -/
theorem mult_centralBinom_nineteen : mult 35345263800 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 19) (s := 531753) (N := 5965) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  decide +kernel

set_option maxRecDepth 8000000 in
/-- `C(40,20) = 137846528820` occurs exactly three times. -/
theorem mult_centralBinom_twenty : mult 137846528820 = 3 := by
  refine mult_centralBinom_eq_three_cubic (m := 20) (s := 1050129) (N := 9388) (by norm_num)
    (choose_eq_iff_descFactorial.2 (by decide)) (lt_choose_of_descFactorial (by decide))
    (by norm_num) (by norm_num) ?_
  refine forall_Ico_glue (b := 3000) (by decide +kernel) ?_
  refine forall_Ico_glue (b := 6000) (by decide +kernel) ?_
  decide +kernel


/-! ## Unconditional consequences below `C(42,21) = 538257874440` -/




open Singmaster in
theorem solution{m : ℕ} (hm : 2 ≤ m) (hm' : m ≤ 20) :
    mult ((2 * m).choose m) = 3 := by
  rcases Nat.lt_or_ge m 11 with hlow | hhigh
  · exact mult_centralBinom_eq_three_of_le_ten hm (by omega)
  · have e11 : (2 * 11).choose 11 = 705432 := choose_eq_iff_descFactorial.2 (by decide)
    have e12 : (2 * 12).choose 12 = 2704156 := choose_eq_iff_descFactorial.2 (by decide)
    have e13 : (2 * 13).choose 13 = 10400600 := choose_eq_iff_descFactorial.2 (by decide)
    have e14 : (2 * 14).choose 14 = 40116600 := choose_eq_iff_descFactorial.2 (by decide)
    have e15 : (2 * 15).choose 15 = 155117520 := choose_eq_iff_descFactorial.2 (by decide)
    have e16 : (2 * 16).choose 16 = 601080390 := choose_eq_iff_descFactorial.2 (by decide)
    have e17 : (2 * 17).choose 17 = 2333606220 := choose_eq_iff_descFactorial.2 (by decide)
    have e18 : (2 * 18).choose 18 = 9075135300 := choose_eq_iff_descFactorial.2 (by decide)
    have e19 : (2 * 19).choose 19 = 35345263800 := choose_eq_iff_descFactorial.2 (by decide)
    have e20 : (2 * 20).choose 20 = 137846528820 := choose_eq_iff_descFactorial.2 (by decide)
    interval_cases m
    · rw [e11]; exact mult_centralBinom_eleven
    · rw [e12]; exact mult_centralBinom_twelve
    · rw [e13]; exact mult_centralBinom_thirteen
    · rw [e14]; exact mult_centralBinom_fourteen
    · rw [e15]; exact mult_centralBinom_fifteen
    · rw [e16]; exact mult_centralBinom_sixteen
    · rw [e17]; exact mult_centralBinom_seventeen
    · rw [e18]; exact mult_centralBinom_eighteen
    · rw [e19]; exact mult_centralBinom_nineteen
    · rw [e20]; exact mult_centralBinom_twenty
