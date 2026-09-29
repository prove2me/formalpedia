-- Prove2me | solution 1 for SheafCohomologyRobustness.delta0_eq_zero_iff_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T00:22:09.958075+00:00
-- url     : https://prove2.me/submissions/2630ff71-7424-4edf-a9c1-93fd35314026

-- Sol generated from MachineLearning/SheafCohomologyRobustness/Cohomology.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_Cohomology
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Discrete Čech Cohomology of a Cover Nerve, and Adversarial Obstructions

This module builds an explicit, fully computable discrete first Čech cohomology
for the two canonical one-dimensional nerves of an open cover:

* the **path nerve** of `n+1` overlapping regions `U₀, U₁, …, Uₙ`
  (consecutive overlaps only), and
* the **cyclic nerve** of `n+1` regions arranged in a loop
  `U₀, …, Uₙ, U₀` (a closed chain of overlaps).

A cover of a neural-network weight space (or of a decision boundary) by linear
activation regions has a nerve.  Local certified-robustness data — one real
number per region (a local certified radius / section value) and a compatible
discrepancy on each overlap — is exactly a Čech `0`- and `1`-cochain.  The
coboundary `δ⁰` measures the failure of local sections to glue.

We prove the two structural facts that drive the whole story:

* `H1_path_vanishes` : on a **tree** nerve (the path) `δ⁰` is *surjective*, i.e.
  `H¹ = 0`.  Every overlap discrepancy is the coboundary of a global potential,
  so local certificates always glue — there is no cohomological obstruction.

* `cyclic_H1_nonvanishing` : on a **loop** nerve `δ⁰` is *not* surjective, i.e.
  `H¹ ≠ 0`.  The obstruction is the holonomy `∑ᵢ gᵢ` around the loop
  (`deltaCyc_sum_zero`, `cyclic_not_coboundary`): a nonzero loop sum is a
  certified-section discrepancy that *cannot* be removed by any global
  reparametrisation.  This nonzero stalk class is precisely a detected
  adversarial vulnerability: a cycle of regions whose local certificates are
  mutually inconsistent.

The kernel computation `delta0_eq_zero_iff_const` identifies `H⁰` with the
constants (a connected nerve has one-dimensional `H⁰`).

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): "Vanishing first cohomology of the cover nerve is
  equivalent to global gluability of local robustness certificates, and the
  obstruction to gluing on a loop is a single scalar holonomy."  Bold form:
  *every* loop in a decision-boundary cover with nonzero holonomy hosts an
  adversarial example.
* Experiment (Experimenter): formalised `δ⁰` on the path nerve and proved
  surjectivity by the explicit potential `f k = ∑_{j<k} gⱼ` (telescoping).
  For the loop, proved `∑ᵢ (δ_cyc f)ᵢ = 0` via the bijection `i ↦ i+1` on
  `Fin (n+1)`, giving a closed-form obstruction.
* Analysis (Analyst): the path proof is a discrete fundamental theorem of
  calculus; the loop obstruction is discrete monodromy.  "True but needed the
  right potential": a naïve recursive potential blew up in `Fin` arithmetic, the
  filter/partial-sum potential is clean.
* Critique (Critic): is `cyclic_H1_nonvanishing` vacuous?  No — it exhibits the
  *constant `1`* cochain (loop sum `n+1 > 0`) as an explicit non-coboundary, so
  the failure of surjectivity is witnessed, not abstract.
* Synthesis (PI): `H¹` of the nerve is the exact ledger of gluability; the path
  certifies, the loop obstructs.
-/


open BigOperators Finset

open SheafCohomologyRobustness

variable {n : ℕ}

/-! ## §1. Cochains and the path coboundary -/





/-! ## §2. Vanishing of `H¹` on the path (tree) nerve -/



/-! ## §3. The cyclic nerve and its cohomological obstruction -/






open SheafCohomologyRobustness in
theorem solution(f : Cochain0 n) :
    delta0 f = 0 ↔ ∀ i j, f i = f j := by
  constructor
  · intro h
    have hstep : ∀ k : Fin n, f k.castSucc = f k.succ := by
      intro k
      have := congrFun h k
      simp only [delta0, Pi.zero_apply] at this
      linarith
    -- every value equals `f 0`
    have hval : ∀ k : Fin (n + 1), f k = f 0 := by
      intro k
      obtain ⟨k, hk⟩ := k
      induction k with
      | zero => rfl
      | succ m ih =>
          have hm : m < n + 1 := Nat.lt_of_succ_lt hk
          have hmn : m < n := Nat.succ_lt_succ_iff.mp hk
          have := hstep ⟨m, hmn⟩
          simp only [Fin.castSucc_mk, Fin.succ_mk] at this
          rw [← this]
          exact ih hm
    intro i j; rw [hval i, hval j]
  · intro h
    funext i
    simp only [delta0, Pi.zero_apply]
    rw [h i.succ i.castSucc]; ring
