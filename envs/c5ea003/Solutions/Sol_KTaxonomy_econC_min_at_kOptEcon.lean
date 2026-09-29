-- Prove2me | solution 1 for KTaxonomy.econC_min_at_kOptEcon
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:24.819538+00:00
-- url     : https://prove2.me/submissions/fa2b1379-5b89-4bbf-a687-7c9c774e7db5

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

/-- The economics optimum location is characterised exactly by `2 ^ k = (T₀ - 1) ln 2 / c_q`. -/
theorem two_rpow_kOptEcon (T₀ cq : ℝ) (hT : 1 < T₀) (hc : 0 < cq) :
    (2 : ℝ) ^ (kOptEcon T₀ cq) = (T₀ - 1) * Real.log 2 / cq := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact Real.rpow_logb (by norm_num) (by norm_num) (div_pos (mul_pos (by linarith) ht) hc)





/-! ## Reproduction of the recorded `exp563` rows -/












open KTaxonomy in
theorem solution(T₀ cq : ℝ) (hT : 1 < T₀) (hc : 0 < cq) (x : ℝ) :
    econC T₀ cq (kOptEcon T₀ cq) ≤ econC T₀ cq x := by
  have hApos : 0 < T₀ - 1 := by linarith
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = kOptEcon T₀ cq := ⟨_, rfl⟩
  have hxsval : (2 : ℝ) ^ xs = (T₀ - 1) * Real.log 2 / cq := by
    rw [hxs]; exact two_rpow_kOptEcon T₀ cq hT hc
  have hneg : (2 : ℝ) ^ (-xs) = cq / ((T₀ - 1) * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), hxsval]
    field_simp
  have hxval : (2 : ℝ) ^ (-x) = ((2:ℝ) ^ (-xs)) * Real.exp (-((x - xs) * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num) (-x), Real.rpow_def_of_pos (by norm_num) (-xs),
      ← Real.exp_add]
    congr 1
    ring
  set u : ℝ := (x - xs) * Real.log 2 with hu
  have hexp : 1 - u ≤ Real.exp (-u) := by
    have := Real.add_one_le_exp (-u); linarith
  have hxu : x = xs + u / Real.log 2 := by
    rw [hu]; field_simp; ring
  have hkey : econC T₀ cq x - econC T₀ cq xs = (cq / Real.log 2) * (u + Real.exp (-u) - 1) := by
    unfold econC
    rw [hxval, hneg, hxu]
    field_simp
    ring
  have hpos : 0 ≤ (cq / Real.log 2) * (u + Real.exp (-u) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  rw [← hxs]
  linarith
