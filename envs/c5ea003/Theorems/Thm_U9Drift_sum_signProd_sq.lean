-- Prove2me | Theorems.Thm_U9Drift_sum_signProd_sq
-- name    : U9Drift.sum_signProd_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:20:30.653788+00:00
-- url     : https://prove2.me/theorems/b6776fc9-652a-4755-b976-a1d638380665
-- title:
--   The total mass of the squared bias.
-- statement:
--   The total mass of the squared bias.
--
--   ```lean
--   theorem U9Drift.sum_signProd_sq(k : ℕ) : ∑ e : Fin k → Bool, signProd e ^ 2 = 4 ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftLocalDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftLocalDensity.lean#L123

-- Thm stub generated from Probability/U9DriftLocalDensity.lean
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# The structural reason the band-9 ratio has mean one but must be clustered by `N`

Context (experiment 569, paper 216).  The measured object is the ratio of the `B`-smooth
rate of the candidate values `j² - N` to the rate of size-matched random controls.  This
file proves the arithmetic facts that govern that ratio at the level of a single small
prime, and the consequence for the inference design.

For an odd prime `p` not dividing `N`, the candidate `j² - N` is divisible by `p` for
`1 + legendreSym p N` residues `j mod p`, i.e. for *two* residues when `N` is a quadratic
residue mod `p` and for *none* otherwise, against exactly one residue for a random integer.
So at every single prime the candidate pool deviates from the control pool by the extreme
factor `2` or `0` — there is no small-perturbation regime.

Main results:

* `U9Drift.sqrtCount_eq` / `U9Drift.localDensity_eq` — the local density of `p | j² - N` is
  `(1 + legendreSym p N)/p`.
* `U9Drift.localDensity_residue` / `U9Drift.localDensity_nonresidue` — it is `2/p` or `0`:
  a `±100%` deviation from the control density `1/p`.
* `U9Drift.two_class_average` — averaged over the two quadratic classes of `N` the local
  density is *exactly* the control density `1/p`.  This is the structural form of the `H0`
  branch: there is no first-order drift for the pooled population, only a rearrangement of
  it across the population of moduli.
* `U9Drift.mean_signProd` / `U9Drift.second_moment_signProd` — modelling the multiplicative
  bias of a modulus by `∏_{i<k} (1 + ε_i)` with independent signs, the mean is `1` while the
  second moment is `2^k`.  Hence `U9Drift.variance_signProd`: the between-modulus variance
  is `2^k - 1`, exponentially large.
* `U9Drift.effective_sample_size_is_the_cluster_count` — consequently the dispersion of the
  pooled estimator is driven by the number of distinct moduli, not by the number of pairs:
  a bootstrap that resamples pairs rather than `N`-clusters understates the spread by an
  exponentially large factor.  This is the quantitative justification of the run's cluster
  bootstrap over its `128` `N`-clusters.
-/

open U9Drift

open Finset

/-! ## The local density of `p ∣ j² - N` -/










/-! ## The multiplicative sign model: mean one, exponentially heavy dispersion -/

theorem U9Drift.sum_signProd_sq(k : ℕ) : ∑ e : Fin k → Bool, signProd e ^ 2 = 4 ^ k := by sorry
