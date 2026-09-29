-- Prove2me | Theorems.Thm_AsaiLargeSieve_periodic_saving
-- name    : AsaiLargeSieve.periodic_saving
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:01:15.516846+00:00
-- url     : https://prove2.me/theorems/76cb0d13-e511-4980-a85e-a0ec3ea84872
-- title:
--   The saving over the trivial constant.
-- statement:
--   **The saving over the trivial constant.**  For the extremal family the trivial
--   Cauchy–Schwarz constant is `D · N`, whereas the optimal one is `D · ⌈N/q⌉`; the periodic
--   criterion therefore saves the full factor `N / ⌈N/q⌉ ≈ q`.  (Stated as the strict inequality
--   `D · ⌈N/q⌉ < D · N`, valid as soon as `D > 0`, `q ≥ 2` and `N ≥ 2`.)
--
--   ```lean
--   theorem AsaiLargeSieve.periodic_saving{q N : ℕ} (hq : 2 ≤ q) (hN : 2 ≤ N) {D : ℝ} (hD : 0 < D) :
--       D * (((N + q - 1) / q : ℕ) : ℝ) < D * (N : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiPeriodicOptimal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiPeriodicOptimal.lean#L195

-- Thm stub generated from Novelty/AsaiPeriodicOptimal.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiPeriodicOptimal
/-
# The periodic large sieve constant is exactly `D · ⌈N/q⌉`

This file continues the formalisation of the analytic skeleton of the paper
**"On the Second Moment of `L(1/2, As(f) × φ)`"** (`Novelty.AsaiLargeSieve`,
`Novelty.AsaiLargeSieveGram`, `Novelty.AsaiSecondMoment`, `Novelty.AsaiMomentApplications`,
`Novelty.AsaiLargeSieveSharp`, `Novelty.AsaiSecondMomentLower`,
`Novelty.AsaiOverlapMultiplicity`).  It settles conjecture **C7** of `FUTURE_DIRECTIONS.md`.

`AsaiLargeSieve.largeSieve_of_periodic_gram_ceil` shows that a `q`-periodic Gram matrix with
entries bounded by `D` admits the large sieve constant `D · ⌈N/q⌉`.  C7 asserted that this
constant is *optimal*: no smaller one is admissible for the extremal periodic family.  That
is proved here.

## Contents

* `AsaiLargeSieve.resFamily` — the extremal `q`-periodic family
  `lam f n = √D · 1_{n ≡ f (mod q)}`, indexed by the residues `f < q`.  Its Gram matrix is
  computed exactly in `gram_resFamily`: it is `D` on `m ≡ n (mod q)` and `0` elsewhere, i.e.
  precisely the extremal matrix allowed by the hypotheses of the periodic criterion.
* `AsaiLargeSieve.largeSieve_resFamily` — the upper bound, an instance of the periodic
  criterion.
* `AsaiLargeSieve.le_of_largeSieve_resFamily` — the matching **lower** bound: every
  admissible constant `C` for this family satisfies `D · ⌈N/q⌉ ≤ C`.  The extremal test
  vector is the indicator of the residue class of `0`, which meets `[0,N)` in at least
  `⌈N/q⌉ = (N + q - 1)/q` points (`ceilDiv_le_card_residue_zero`), and on which the quadratic
  form takes the value `D · k²` against a coefficient mass `k`
  (`sum_normSq_linForm_resFamily`, `sum_normSq_resIndicator`).
* `AsaiLargeSieve.isLeast_periodic_constant` — the two halves combined: `D · ⌈N/q⌉` is the
  *least* admissible large sieve constant for `resFamily`.  In particular the criterion
  `largeSieve_of_periodic_gram_ceil` cannot be improved, and — by
  `ceilDiv_lt_real_of_not_dvd` — the older constant `D · (N/q + 1)` is genuinely
  suboptimal whenever `q ∤ N`.
* `AsaiLargeSieve.periodic_saving` — the quantitative gain over the trivial constant: for the
  extremal family the trivial (Cauchy–Schwarz) constant is `D · N`, so the periodic criterion
  saves a factor of essentially `q`.
-/

open Finset Complex

open AsaiLargeSieve

theorem AsaiLargeSieve.periodic_saving{q N : ℕ} (hq : 2 ≤ q) (hN : 2 ≤ N) {D : ℝ} (hD : 0 < D) :
    D * (((N + q - 1) / q : ℕ) : ℝ) < D * (N : ℝ) := by sorry
