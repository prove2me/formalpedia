-- Prove2me | Definitions.Def_Novelty_SuperExponential
-- name    : Novelty_SuperExponential
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:03.227075+00:00
-- url     : https://prove2.me/theorems/1fd3a425-8969-47b0-bc57-9e059279363f
-- title:
--   Aether Catalog definitions — Novelty_SuperExponential
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SuperExponential`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SuperExponential.lean by skeleton subtraction
import Mathlib
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

namespace Novelty.SCD

/-- A sequence `f : ℕ → ℕ` grows **super-exponentially** if it Filter.eventually exceeds
every fixed exponential `c ^ n`. -/
def SuperExp (f : ℕ → ℕ) : Prop :=
  ∀ c : ℕ, ∃ N, ∀ n, N ≤ n → c ^ n < f n





/-
A fixed polynomial `m ↦ m ^ k` is **not** super-exponential: taking base
`c = 2`, the exponential `2 ^ m` Filter.eventually overtakes `m ^ k`, so `m ^ k` fails to
exceed `2 ^ m` for large `m`.  This guarantees `SuperExp` is a strict dividing
line (it rules out every polynomial).
-/

end Novelty.SCD


