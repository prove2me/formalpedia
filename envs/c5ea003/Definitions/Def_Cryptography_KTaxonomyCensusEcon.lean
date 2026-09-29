-- Prove2me | Definitions.Def_Cryptography_KTaxonomyCensusEcon
-- name    : Cryptography_KTaxonomyCensusEcon
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:18:33.239685+00:00
-- url     : https://prove2.me/theorems/98aca7e4-cfd1-4c3e-889f-c7bbb355fa60
-- title:
--   Aether Catalog definitions — Cryptography_KTaxonomyCensusEcon
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.KTaxonomyCensusEcon`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/KTaxonomyCensusEcon.lean by skeleton subtraction
import Mathlib

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

namespace KTaxonomy

open Real

/-! ## Definitions -/

/-- The **pin**: `⌈log₂ W⌉`, the budget at which a support of width `W` is fully resolved.
Marginal gain past this point is exactly zero.  It is a saturation point, never an optimum. -/
def kPin (W : ℕ) : ℕ := Nat.clog 2 W

/-- The T2 **census** total cost of a `k`-query halving schedule on support width `W`:
`k` queries plus the residual, priced at half the remaining support (`+ 1/2` convention). -/
noncomputable def census (W : ℝ) (k : ℕ) : ℝ := k + (W / 2 ^ k + 1) / 2

/-- The **economics** cost of a `k`-query schedule: `k + 1` charged at unit price `c_q`,
plus the expected residual scan against the measured baseline `T₀`. -/
noncomputable def econ (T₀ cq : ℝ) (k : ℕ) : ℝ := cq * (1 + k) + (T₀ - 1) / 2 ^ k

/-- Continuous (real-exponent) version of `census`. -/
noncomputable def censusC (W x : ℝ) : ℝ := x + (W * (2 : ℝ) ^ (-x) + 1) / 2

/-- Continuous (real-exponent) version of `econ`. -/
noncomputable def econC (T₀ cq x : ℝ) : ℝ := cq * (1 + x) + (T₀ - 1) * (2 : ℝ) ^ (-x)

/-- Continuous location of the economics optimum: `log₂ ((T₀ - 1) ln 2 / c_q)`. -/
noncomputable def kOptEcon (T₀ cq : ℝ) : ℝ := logb 2 ((T₀ - 1) * Real.log 2 / cq)

/-- Continuous location of the census optimum: `log₂ (W ln 2) - 1`. -/
noncomputable def kOptCost (W : ℝ) : ℝ := logb 2 (W * Real.log 2) - 1

/-! ## Consistency of the discrete and continuous costs -/




/-! ## The exact identities relating the two objectives -/






/-! ## A discrete convexity principle -/

section DiscreteConvexity

variable {f : ℕ → ℝ}





end DiscreteConvexity

/-! ## Discrete convexity of the two objectives -/



/-! ## The dyadic census optimum: exact value `log₂ W + 1/2` on a two-element tie set -/









/-! ## The pin is never an optimum -/





/-! ## The continuous optima -/






/-! ## Reproduction of the recorded `exp563` rows -/

/-- Balanced run: measured baseline `T̄₀ = 1072.425`. -/
noncomputable def T0bal : ℝ := 1072425 / 1000

/-- Unbalanced run: measured baseline `T̄₀ = 286205.89`. -/
noncomputable def T0unb : ℝ := 28620589 / 100









end KTaxonomy


