-- Prove2me | Theorems.Thm_Novelty_SCD_pow_const_not_superexp
-- name    : Novelty.SCD.pow_const_not_superexp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:16:36.775873+00:00
-- url     : https://prove2.me/theorems/3ed56a2e-1b5d-4ed1-8c6b-f99cf2e86e61
-- title:
--   Pow const not superexp
-- statement:
--   Formal statement of `Novelty.SCD.pow_const_not_superexp` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Novelty.SCD.pow_const_not_superexp(k : ℕ) : ¬ SuperExp (fun m => m ^ k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SuperExponential.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SuperExponential.lean#L102

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






/-
A fixed polynomial `m ↦ m ^ k` is **not** super-exponential: taking base
`c = 2`, the exponential `2 ^ m` Filter.eventually overtakes `m ^ k`, so `m ^ k` fails to
exceed `2 ^ m` for large `m`.  This guarantees `SuperExp` is a strict dividing
line (it rules out every polynomial).
-/

theorem Novelty.SCD.pow_const_not_superexp(k : ℕ) : ¬ SuperExp (fun m => m ^ k) := by sorry
