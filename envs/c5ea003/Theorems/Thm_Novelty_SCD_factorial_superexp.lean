-- Prove2me | Theorems.Thm_Novelty_SCD_factorial_superexp
-- name    : Novelty.SCD.factorial_superexp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:16:28.263313+00:00
-- url     : https://prove2.me/theorems/dbe7d4b3-b440-4f6b-9f6f-0b7691b0b90a
-- title:
--   The factorial is super-exponential.
-- statement:
--   The factorial is super-exponential.  Proof: for fixed base `c`, the real
--   sequence `c^n / n!` tends to `0`, so it is Filter.eventually `< 1`, i.e. `c^n < n!`.
--
--   ```lean
--   theorem Novelty.SCD.factorial_superexp: SuperExp Nat.factorial := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SuperExponential.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SuperExponential.lean#L52

-- Thm stub generated from Novelty/SuperExponential.lean
import Mathlib
import Definitions.Def_Novelty_SuperExponential
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Super-exponential growth: the analytic engine

This file isolates the notion of *super-exponential* growth of a natural-number
sequence and proves the facts that drive the rest of the project:

* `factorial_superexp` : the factorial `n ↦ n!` is super-exponential.
* `perm_card_superexp` : the number of permutations of an `n`-element set,
  `Fintype.card (Equiv.Perm (Fin n)) = n!`, is super-exponential.

`SuperExp f` is defined as: for every base `c`, the sequence `f` Filter.eventually
exceeds `c ^ n`.  This is precisely the property "grows faster than any fixed
exponential" used in the conjecture on the number of symmetric chain
decompositions of `M(n)`.

We also record:

* `SuperExp.of_eventually_le` : super-exponential growth transfers upward along
  an eventual pointwise inequality (used to push a *lower bound* on a count to
  super-exponential growth of the count itself);
* `pow_const_not_superexp` : a fixed polynomial `m ↦ m ^ k` is *not*
  super-exponential — the sharp contrast that makes the super-exponential claim
  non-vacuous.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): "Super-exponential" should mean: dominates every
exponential `c^n`.  Conjecture: factorial witnesses this, and so does any count
bounded below by a factorial.
EXPERIMENT (Experimenter): `FloorSemiring.tendsto_pow_div_factorial_atTop`
provides `c^n / n! → 0`, from which the discrete inequality `c^n < n!` for large
`n` falls out by unpacking the metric definition of the limit.
ANALYSIS (Analyst): the analytic limit is the cleanest engine — an elementary
induction needs a base case `c^{N} < N!` whose threshold `N ≈ e·c` is awkward to
pin down uniformly in `c`.  The limit sidesteps the base case entirely.
CRITIQUE (Critic): is the statement vacuous?  No: `pow_const_not_superexp`
exhibits explicit functions (`m^k`) that fail `SuperExp`, so the predicate is a
genuine dividing line, not satisfied by everything.
-/

open Filter Topology

open Novelty.SCD

theorem Novelty.SCD.factorial_superexp: SuperExp Nat.factorial := by sorry
