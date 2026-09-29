-- Prove2me | solution 1 for WeilDualitySign.Witnesses.cycle4_mixed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:36.584213+00:00
-- url     : https://prove2.me/submissions/409f905b-589a-4eeb-aae2-ef4738faa310

-- Sol generated from Applications/WeilDualitySign/Witnesses.lean
import Mathlib
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel
import Definitions.Def_Applications_WeilDualitySign_Witnesses
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
theorem solution(a : ℂ) (ha : a ≠ 0) :
    (mixed Q hQ a ha).deg = 4 ∧
    (∏ i, (mixed Q hQ a ha).α i) = -Q ^ 4 ∧
    (mixed Q hQ a ha).rootSign = -1 ∧
    (mixed Q hQ a ha).rootSign ≠ (-1 : ℂ) ^ (mixed Q hQ a ha).deg := by
  have hprod : (∏ i, (mixed Q hQ a ha).α i) = -Q ^ 4 := by
    simp [mixed, Fin.prod_univ_four]
    field_simp
  have hsign : (mixed Q hQ a ha).rootSign = -1 := by
    simp only [DualEigensystem.rootSign, DualEigensystem.deg, Fintype.card_fin]
    rw [hprod]
    simp only [mixed]
    field_simp
  refine ⟨rfl, hprod, hsign, ?_⟩
  rw [hsign]
  simp only [DualEigensystem.deg, Fintype.card_fin]
  norm_num
