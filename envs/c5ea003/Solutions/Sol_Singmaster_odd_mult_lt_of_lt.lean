-- Prove2me | solution 1 for Singmaster.odd_mult_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:56:18.515008+00:00
-- url     : https://prove2.me/submissions/acf6edd4-c2ef-463f-8f3e-c2f304f834e4

-- Sol generated from Combinatorics/SingmasterCentralBinomial.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_centralBinom_monotone
import Theorems.Thm_Singmaster_mult_centralBinom_eq_three_of_le_ten
import Theorems.Thm_Singmaster_mult_two
import Theorems.Thm_Singmaster_odd_mult_iff_centralBinom
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











/-! ## Unconditional consequences below `C(22,11) = 705432` -/




open Singmaster in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem solution{t : ℕ} (ht : 2 ≤ t) (hlt : t < 705432) (hodd : Odd (mult t)) :
    mult t = 1 ∨ mult t = 3 := by
  obtain ⟨m, hm⟩ := (odd_mult_iff_centralBinom ht).1 hodd
  have hm10 : m ≤ 10 := by
    by_contra hc
    push_neg at hc
    have hmono : (2 * 11).choose 11 ≤ (2 * m).choose m := centralBinom_monotone (by omega)
    have hval : (2 * 11).choose 11 = 705432 := by decide
    omega
  rcases Nat.lt_or_ge m 2 with hlow | hge
  · have e0 : (2 * 0).choose 0 = 1 := by decide
    have e1 : (2 * 1).choose 1 = 2 := by decide
    interval_cases m
    · rw [e0] at hm; omega
    · rw [e1] at hm
      subst hm
      exact Or.inl mult_two
  · rw [hm, mult_centralBinom_eq_three_of_le_ten hge hm10]
    exact Or.inr rfl
