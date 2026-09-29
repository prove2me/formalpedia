-- Prove2me | solution 1 for Singmaster.mult_centralBinom_eq_three_of_le_ten
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:34:09.928077+00:00
-- url     : https://prove2.me/submissions/c51ad727-cd10-4eee-8e0e-ca19016eb0b9

-- Sol generated from Combinatorics/SingmasterCentralBinomial.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_mult_centralBinom_eq_three
import Theorems.Thm_Singmaster_mult_six
/-
# Central binomial coefficients occur exactly three times (verified initial segment)

Fourth research cycle, building on

* `Combinatorics.SingmasterOccurrences` (the occurrence set `occ`, the multiplicity
  `mult`, monotonicity and growth of binomial coefficients),
* `Combinatorics.SingmasterRefinements` (strict unimodality of a row),
* `Combinatorics.SingmasterParity` (the parity criterion: `N(t)` is odd iff `t` is a
  central binomial coefficient).

The parity criterion reduced the open question "does any number occur exactly five or
exactly seven times?" to the single sequence `C(2m,m) = 2, 6, 20, 70, 252, 924, …`.
This file makes that reduction *effective* and then executes it for `m ≤ 10`.

## The effective criterion

For `t = C(2m,m)` with `m ≥ 2` we prove a **sandwich theorem**
(`Singmaster.choose_lt_centralBinom`): every entry `C(n,k)` with `n ≤ 2m` other than
the central entry itself is *strictly smaller* than `t`.  Hence any further occurrence
of `t` lies in a row `n > 2m`, and being an interior entry it satisfies
`C(n,2) ≤ C(n,k) = t`, which caps `n` by an explicit `N` with `t < C(N,2)`.

So the multiplicity of `C(2m,m)` is exactly three as soon as a *finite, explicitly
bounded* search over `2m < n < N`, `2 ≤ k ≤ n/2` finds no further occurrence
(`Singmaster.mult_centralBinom_eq_three`).  The search is phrased with
`Nat.descFactorial` rather than `Nat.choose`, which is what makes it feasible for the
kernel: `C(n,k) = t` is equivalent to `n.descFactorial k = k ! * t`, and the descending
factorial costs `k` multiplications instead of `C(n,k)` additions.

## Results

* `Singmaster.mult_centralBinom_eq_three` — the effective criterion;
* `Singmaster.mult_centralBinom_eq_three_of_le_ten` — `N(C(2m,m)) = 3` for `2 ≤ m ≤ 10`,
  i.e. for `6, 20, 70, 252, 924, 3432, 12870, 48620, 184756`;
* `Singmaster.mult_ne_five_or_seven_of_lt` — **unconditionally, no `t < 705432` occurs
  exactly five or exactly seven times**.  This is the machine-checked version of the
  empirical observation quoted in the problem statement, and it is obtained from only
  ten finite searches rather than from a scan of all `t`;
* `Singmaster.odd_mult_lt_of_lt` — below `705432` an odd multiplicity is `1` or `3`.
-/

open Finset

open Singmaster

/-! ## Basic size estimates for `C(2m,m)` -/





/-! ## The sandwich theorem -/


/-! ## The effective criterion -/



/-! ## Executing the criterion for `m ≤ 10`

Each of the following is a genuine finite search over the explicitly bounded window
produced by the criterion; the windows are empty for `m = 2, 3` and grow to
`20 < n < 609` for `m = 10`. -/

theorem mult_centralBinom_two : mult 6 = 3 := mult_six

set_option maxRecDepth 4000 in
theorem mult_centralBinom_three : mult 20 = 3 := by
  have h : (2 * 3).choose 3 = 20 := by decide
  have := mult_centralBinom_eq_three (m := 3) (N := 7) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 4000 in
theorem mult_centralBinom_four : mult 70 = 3 := by
  have h : (2 * 4).choose 4 = 70 := by decide
  have := mult_centralBinom_eq_three (m := 4) (N := 13) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 40000 in
theorem mult_centralBinom_five : mult 252 = 3 := by
  have h : (2 * 5).choose 5 = 252 := by decide
  have := mult_centralBinom_eq_three (m := 5) (N := 23) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 100000 in
theorem mult_centralBinom_six : mult 924 = 3 := by
  have h : (2 * 6).choose 6 = 924 := by decide
  have := mult_centralBinom_eq_three (m := 6) (N := 44) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 200000 in
theorem mult_centralBinom_seven : mult 3432 = 3 := by
  have h : (2 * 7).choose 7 = 3432 := by decide
  have := mult_centralBinom_eq_three (m := 7) (N := 84) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 400000 in
theorem mult_centralBinom_eight : mult 12870 = 3 := by
  have h : (2 * 8).choose 8 = 12870 := by decide
  have := mult_centralBinom_eq_three (m := 8) (N := 161) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxRecDepth 2000000 in
theorem mult_centralBinom_nine : mult 48620 = 3 := by
  have h : (2 * 9).choose 9 = 48620 := by decide
  have := mult_centralBinom_eq_three (m := 9) (N := 313) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
theorem mult_centralBinom_ten : mult 184756 = 3 := by
  have h : (2 * 10).choose 10 = 184756 := by decide
  have := mult_centralBinom_eq_three (m := 10) (N := 609) (by norm_num) (by norm_num)
    (by decide) (by decide)
  rwa [h] at this


/-! ## Unconditional consequences below `C(22,11) = 705432` -/




open Singmaster in
theorem solution{m : ℕ} (hm : 2 ≤ m) (hm' : m ≤ 10) :
    mult ((2 * m).choose m) = 3 := by
  have e2 : (2 * 2).choose 2 = 6 := by decide
  have e3 : (2 * 3).choose 3 = 20 := by decide
  have e4 : (2 * 4).choose 4 = 70 := by decide
  have e5 : (2 * 5).choose 5 = 252 := by decide
  have e6 : (2 * 6).choose 6 = 924 := by decide
  have e7 : (2 * 7).choose 7 = 3432 := by decide
  have e8 : (2 * 8).choose 8 = 12870 := by decide
  have e9 : (2 * 9).choose 9 = 48620 := by decide
  have e10 : (2 * 10).choose 10 = 184756 := by decide
  interval_cases m
  · rw [e2]; exact mult_centralBinom_two
  · rw [e3]; exact mult_centralBinom_three
  · rw [e4]; exact mult_centralBinom_four
  · rw [e5]; exact mult_centralBinom_five
  · rw [e6]; exact mult_centralBinom_six
  · rw [e7]; exact mult_centralBinom_seven
  · rw [e8]; exact mult_centralBinom_eight
  · rw [e9]; exact mult_centralBinom_nine
  · rw [e10]; exact mult_centralBinom_ten
