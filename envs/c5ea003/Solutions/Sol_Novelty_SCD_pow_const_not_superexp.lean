-- Prove2me | solution 1 for Novelty.SCD.pow_const_not_superexp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:47.824968+00:00
-- url     : https://prove2.me/submissions/8006655b-72d5-4033-8394-83024b33dfed

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
theorem solution(k : ℕ) : ¬ SuperExp (fun m => m ^ k) := by
  intro h
  obtain ⟨N, hN⟩ := h 2
  have h_contra : ∃ n ≥ N, n ^ k < 2 ^ n := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k / 2 ^ n) Filter.atTop (nhds 0) := by
      -- We can convert this limit into a form that is easier to handle by substituting $m = n \log 2$.
      suffices h_log : Filter.Tendsto (fun m : ℝ => (m / Real.log 2) ^ k / Real.exp m) Filter.atTop (nhds 0) by
        convert h_log.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) ) using 2 ; norm_num [ Real.exp_nat_mul, Real.exp_log ];
      -- We can factor out $(1 / \log 2)^k$ from the limit.
      suffices h_factor : Filter.Tendsto (fun m : ℝ => m ^ k / Real.exp m) Filter.atTop (nhds 0) by
        convert h_factor.div_const ( Real.log 2 ^ k ) using 2 <;> ring;
      simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
    have := h_lim.eventually ( gt_mem_nhds zero_lt_one ) ; have := this.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ n, hn₁, hn₂ ⟩ := this.exists; use n; norm_num at *; rw [ div_lt_iff₀ ] at * <;> norm_cast at * <;> aesop;
  obtain ⟨n, hn1, hn2⟩ := h_contra
  linarith [hN n hn1]
