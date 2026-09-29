-- Prove2me | solution 1 for Novelty.SCD.SuperExp.of_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:46.126607+00:00
-- url     : https://prove2.me/submissions/faf6b67c-608a-4961-b25c-3367eaef569e

-- Sol generated from Novelty/SuperExponential.lean
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


open Novelty.SCD in
theorem solution{f g : ℕ → ℕ} (hf : SuperExp f)
    (h : ∃ M, ∀ n, M ≤ n → f n ≤ g n) : SuperExp g := by
  obtain ⟨M, hM⟩ := h
  intro c
  obtain ⟨N, hN⟩ := hf c
  refine ⟨max N M, fun n hn => ?_⟩
  have hn1 : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : M ≤ n := le_trans (le_max_right _ _) hn
  exact lt_of_lt_of_le (hN n hn1) (hM n hn2)
