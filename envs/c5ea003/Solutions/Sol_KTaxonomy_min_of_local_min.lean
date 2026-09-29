-- Prove2me | solution 1 for KTaxonomy.min_of_local_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:32:54.444462+00:00
-- url     : https://prove2.me/submissions/086025b8-17a9-4668-8002-941e40163313

-- Sol generated from Cryptography/KTaxonomyCensusEcon.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon
import Theorems.Thm_KTaxonomy_mono_left

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

/-- Monotone increments: the discrete-convexity hypothesis propagates along `≤`. -/
lemma incr_mono (hconv : ∀ k, f (k + 1) - f k ≤ f (k + 2) - f (k + 1)) {i j : ℕ} (hij : i ≤ j) :
    f (i + 1) - f i ≤ f (j + 1) - f j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans ih (by simpa using hconv n)

/-- A discretely convex function is nondecreasing to the right of a nonnegative increment. -/
lemma mono_right (hconv : ∀ k, f (k + 1) - f k ≤ f (k + 2) - f (k + 1)) {n : ℕ}
    (hup : f n ≤ f (n + 1)) : ∀ k, n ≤ k → f n ≤ f k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
      have := incr_mono hconv hm
      linarith




/-! ## Discrete convexity of the two objectives -/



/-! ## The dyadic census optimum: exact value `log₂ W + 1/2` on a two-element tie set -/









/-! ## The pin is never an optimum -/





/-! ## The continuous optima -/






/-! ## Reproduction of the recorded `exp563` rows -/












open KTaxonomy in
theorem solution(hconv : ∀ k, f (k + 1) - f k ≤ f (k + 2) - f (k + 1)) {n : ℕ}
    (hup : f n ≤ f (n + 1)) (hdown : ∀ m, n = m + 1 → f n ≤ f m) : ∀ k, f n ≤ f k := by
  intro k
  rcases le_or_gt n k with h | h
  · exact mono_right hconv hup k h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact mono_left hconv (hdown m rfl) k (by omega)
