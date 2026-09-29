-- Prove2me | solution 1 for WeilDualitySign.Witnesses.twoNegFixed_deg_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:37.602245+00:00
-- url     : https://prove2.me/submissions/624a1edb-8a0f-44d3-9a83-76872c0819c3

-- Sol generated from Applications/WeilDualitySign/Witnesses.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Definitions.Def_Applications_WeilDualitySign_Witnesses
import Theorems.Thm_WeilDualitySign_DualEigensystem_mem_negFixed
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpness Witnesses for the Duality Sign Law

This file is the adversarial half of `EigenvalueModel.lean`.  There we proved

  `∏ α_i = (−1)^{#neg-fixed} · Q^d`,   `ε = (−1)^{d + #neg-fixed}`,

and the mission conjecture as the corollary "no `−Q` fixed point ⟹ `∏ α_i = Q^d`,
`ε = (−1)^d`".  Here we exhibit explicit complex eigensystems showing that **every
hypothesis is load-bearing and the theorem is sharp**:

* `posFixed_deg_one` — degree 1 with the fixed point `α = +Q`: `∏ α = Q`, `ε = −1`.
  This is the `d = 1` sign the conjecture predicts.
* `negFixed_deg_one` — degree 1 with the fixed point `α = −Q`: `∏ α = −Q ≠ Q` and
  `ε = +1 ≠ (−1)^1`.  A *single* anti-diagonal fixed point flips the sign, so the
  hypothesis of the conjecture cannot be deleted.
* `pair_deg_two` — a free duality 2-cycle `{a, Q²/a}`: `∏ α = Q²`, `ε = +1`, valid for
  every `a ≠ 0`.  2-cycles are sign-neutral, whatever the eigenvalues are.
* `twoNegFixed_deg_two` — two `−Q` fixed points: the hypothesis of the conjecture
  *fails* yet the conclusion `∏ α = Q²` still *holds*.  The hypothesis is therefore
  sufficient but not necessary — only the parity matters.
* `cycle4_two_pairs` and `cycle4_mixed` — the degree-4 witnesses: two duality
  2-cycles give `ε = +1 = (−1)^4`, while `(+Q, −Q, a, Q²/a)` gives `ε = −1 ≠ (−1)^4`.
* `three_cycle_no_fixed_point_sign_flip` — the deepest one: a *non-involutive* duality
  (a 3-cycle) with **no fixed points at all** — so the mission hypothesis holds
  vacuously — yet `∏ α = −Q³`.  Involutivity of `σ` is not decorative: it is exactly
  what the pairing argument consumes.

-- !-- Lab Notes -- !--
Experiment (Experimenter): the search for a counterexample to the conjecture was run
  by hand over all duality structures of degree ≤ 4 (`ε` depends only on `d` and the
  fixed-point data, so degree 4 already exhibits every pattern: 4 fixed points,
  2 fixed + one 2-cycle, two 2-cycles).  All conform to `ε = (−1)^{d + #neg-fixed}`.
Analysis (Analyst): the only way to break the conclusion while keeping the stated
  hypothesis is to break *involutivity*.  Chasing `α_i α_{σ i} = Q²` around a 3-cycle
  forces `α_0 = α_2` and then `α_0² = Q²`, so the whole cycle is constant `±Q`; the
  choice `−Q` yields `∏ α = −Q³` with an empty fixed-point set.
Critique (Critic): all witnesses are genuine inhabitants of `DualEigensystem` (the
  3-cycle one is stated separately, precisely because it is not one), and each claim
  is an equation between explicit complex numbers, not a vacuous implication.
-/

open Finset

open WeilDualitySign

open Witnesses

variable (Q : ℂ) (hQ : Q ≠ 0)

/-! ### Degree 1: the two self-dual eigenvalues -/





/-! ### Degree 2: a free duality pair, and two anti-diagonal fixed points -/





/-! ### Degree 4: the cycle-4 witnesses -/





/-! ### Involutivity is essential: a fixed-point-free 3-cycle with `∏ α = −Q³` -/




open WeilDualitySign.Witnesses in
theorem solution:
    (twoNegFixed Q hQ).negFixed = univ ∧
    (twoNegFixed Q hQ).negFixed.card = 2 ∧
    ¬ (∀ i, (twoNegFixed Q hQ).σ i = i → (twoNegFixed Q hQ).α i ≠ -(twoNegFixed Q hQ).Q) ∧
    (∏ i, (twoNegFixed Q hQ).α i) = (twoNegFixed Q hQ).Q ^ (twoNegFixed Q hQ).deg ∧
    (twoNegFixed Q hQ).rootSign = 1 := by
  have huniv : (twoNegFixed Q hQ).negFixed = univ :=
    Finset.eq_univ_iff_forall.mpr fun i =>
      (twoNegFixed Q hQ).mem_negFixed.mpr ⟨rfl, rfl⟩
  have hcard : (twoNegFixed Q hQ).negFixed.card = 2 := by
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hprod : (∏ i, (twoNegFixed Q hQ).α i) = Q ^ 2 := by
    simp [twoNegFixed]
  refine ⟨huniv, hcard, ?_, ?_, ?_⟩
  · intro h
    exact h 0 rfl rfl
  · rw [hprod]; rfl
  · simp only [DualEigensystem.rootSign, DualEigensystem.deg, Fintype.card_fin]
    rw [hprod]
    simp only [twoNegFixed]
    field_simp
