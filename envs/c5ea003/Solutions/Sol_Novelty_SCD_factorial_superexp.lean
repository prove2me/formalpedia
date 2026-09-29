-- Prove2me | solution 1 for Novelty.SCD.factorial_superexp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:46.69971+00:00
-- url     : https://prove2.me/submissions/5ed06cfb-4dff-4c17-baaa-cfa7a7706ce6

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
theorem solution: SuperExp Nat.factorial := by
  intro c
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop (c : ℝ)
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  simp only [Real.dist_eq, sub_zero] at hd
  have hpos : (0 : ℝ) < n.factorial := by positivity
  have hcn : (c : ℝ) ^ n / n.factorial < 1 := by
    have := (abs_lt.mp hd).2
    linarith [abs_nonneg ((c : ℝ) ^ n / n.factorial)]
  rw [div_lt_one hpos] at hcn
  have hcast : ((c ^ n : ℕ) : ℝ) < ((n.factorial : ℕ) : ℝ) := by push_cast; exact hcn
  exact_mod_cast hcast
