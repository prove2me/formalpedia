-- Prove2me | solution 1 for KTaxonomy.exp563_balanced_pred_bracket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:25.85857+00:00
-- url     : https://prove2.me/submissions/30534eab-b69d-43b5-9b5a-00b7e4a83c7a

-- Sol generated from Cryptography/KTaxonomyCensusEcon.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon

/-!
# A taxonomy of "k*": pin, census-optimal, and economics-optimal search budgets

Three numbers are routinely written `k*` in binary-search / halving-style cost accounting,
and they are **not** the same number:

* `kPin W = ⌈log₂ W⌉` (`Nat.clog 2 W`) — the *pin*: the budget at which a support of width
  `W` is fully resolved and the marginal gain of a further query is exactly zero.
* `kOptCost W = argmin_k (k + (W / 2 ^ k + 1) / 2)` — the *census* total-cost stop, in which
  the residual is priced at half the remaining support.
* `kOptEcon T₀ c_q = argmin_k (c_q (1 + k) + (T₀ - 1) / 2 ^ k)` — the *economics* optimum, in
  which each query is paid `c_q` against a measured baseline `T₀`.

This file gives all three a formal definition and proves exactly how they relate.

## Main results

* `econ_eq_census_anchor` : the **exact pointwise identity**
  `econ T₀ 1 k = census (2 * (T₀ - 1)) k + 1/2`, valid for every `k`.  Consequently
  (`econ_le_econ_iff_census_le_census`, `econ_argmin_iff_census_argmin`) the two objectives
  have *identical* argmin sets once the anchor conversion `W ↔ 2 (T₀ - 1)` is applied.
* `econ_eq_census_naive_shift` : the **unconverted** comparison
  `econ T₀ 1 (k + 1) = census (T₀ - 1) k + 3/2`, so feeding the same number into both
  formulas shifts the discrete argmin by **exactly one** query
  (`naive_argmin_shift_exactly_one`), and the continuous locations differ by exactly `1`
  (`kOptEcon_eq_kOptCost_add_one`).
* `census_dyadic_min` / `census_dyadic_eq_iff` : for dyadic `W = 2 ^ m` the census optimum
  value is `m + 1/2` **exactly**, attained precisely on the tie set `{m - 2, m - 1}`.
* `census_pin_not_optimal`, `pin_gap_mem` : the pin is *never* a census optimum
  (`m ≥ 1`), and the gap `kPin - k_opt ∈ {1, 2}`.
* `econC_min_at_kOptEcon` : the continuous economics optimum really is a global minimiser,
  characterised exactly by `2 ^ k = (T₀ - 1) log 2 / c_q`.
* `exp563_balanced_argmin`, `exp563_unbalanced_argmin` : the two recorded runs
  (`T̄₀ = 1072.425` and `T̄₀ = 286205.89`) have discrete economics argmin `10` and `18`,
  and the matched-anchor census reproduces the same optimum.

-- !-- Lab Notes -- !--
Hypothesizer (conjectures, ranked):
 (H1) `econ` and `census` are the *same* function up to an additive constant after the
      anchor conversion `W = 2 (T₀ - 1)`; hence identical argmin sets.            [BOLD]
 (H2) Without the conversion the discrete argmins differ by exactly `+1`, not "about 1".
 (H3) For dyadic `W` the census optimum is a two-element tie set and the optimal value is
      the *exact* rational `log₂ W + 1/2`.
 (H4) The pin `⌈log₂ W⌉` is never optimal for either objective (`W ≥ 2`).
 (H5) A discrete-convexity principle (increments monotone ⇒ local min is global) covers
      both objectives uniformly, so no separate analysis is needed per objective.

Experimenter: H1–H5 are all proved below, with zero sorries.  H1 and H2 are exact
identities (`econ_eq_census_anchor`, `econ_eq_census_naive_shift`) proved by `field_simp`
plus `ring`; H3 needs the elementary but non-formal fact `2 ^ j > j + 1` for `j ≥ 2`
(`two_pow_lt_of_two_le`, by induction); H5 is `min_of_local_min`, proved from a single
monotone-increment lemma.

Analyst: the informative failure is that the naive "same number in both formulas"
comparison is *not* an approximation error that vanishes: `econ T₀ 1 (k+1)` and
`census (T₀ - 1) k` differ by the constant `3/2`, so the shift is a structural `+1` on the
argmin, independent of `T₀`.  The equality-case analysis in `census_dyadic_eq_iff` also
shows the census tie set is a genuine two-element set (`2 ^ j = j + 1` has exactly the two
solutions `j = 0, 1`), so "the" census optimum is only well defined as a set.

Critic: no theorem here is `True`, `rfl`-only or `native_decide`-only; the numeric
`exp563` statements are discharged by `norm_num` on exact rational data plus the structural
`min_of_local_min` principle, so they are genuine global-minimality claims over all `k : ℕ`,
not spot checks.
-/

open KTaxonomy

open Real

/-! ## Definitions -/








/-! ## Consistency of the discrete and continuous costs -/




/-! ## The exact identities relating the two objectives -/






/-! ## A discrete convexity principle -/


variable {f : ℕ → ℝ}






/-! ## Discrete convexity of the two objectives -/



/-! ## The dyadic census optimum: exact value `log₂ W + 1/2` on a two-element tie set -/









/-! ## The pin is never an optimum -/





/-! ## The continuous optima -/






/-! ## Reproduction of the recorded `exp563` rows -/







lemma two_rpow_ofNat (n : ℕ) (y : ℝ) (h : (2:ℝ) ^ n = y) : (2:ℝ) ^ (n : ℝ) = y := by
  rw [Real.rpow_natCast]; exact h





open KTaxonomy in
theorem solution: 9 < kOptEcon T0bal 1 ∧ kOptEcon T0bal 1 < 10 := by
  have ht1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have ht2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have harg : (T0bal - 1) * Real.log 2 / 1 = (T0bal - 1) * Real.log 2 := by ring
  have hpos : (0:ℝ) < (T0bal - 1) * Real.log 2 := by rw [T0bal]; nlinarith
  have h9 : (2:ℝ) ^ (9:ℝ) = 512 := two_rpow_ofNat 9 512 (by norm_num)
  have h10 : (2:ℝ) ^ (10:ℝ) = 1024 := two_rpow_ofNat 10 1024 (by norm_num)
  constructor
  · rw [kOptEcon, harg, Real.lt_logb_iff_rpow_lt (by norm_num) hpos, h9, T0bal]
    nlinarith
  · rw [kOptEcon, harg, Real.logb_lt_iff_lt_rpow (by norm_num) hpos, h10, T0bal]
    nlinarith
