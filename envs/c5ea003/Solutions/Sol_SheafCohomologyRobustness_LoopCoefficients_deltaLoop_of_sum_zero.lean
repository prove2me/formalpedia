-- Prove2me | solution 1 for SheafCohomologyRobustness.LoopCoefficients.deltaLoop_of_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:52:36.004829+00:00
-- url     : https://prove2.me/submissions/eb5ef1e5-d3a6-4be9-8fdd-7131406463c2

-- Sol generated from MachineLearning/SheafCohomologyRobustness/LoopCoefficients.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_LoopCoefficients
import Theorems.Thm_SheafCohomologyRobustness_LoopCoefficients_partialSumM_succ
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# `H¹` of the Loop Nerve with Arbitrary Coefficients, and the `ℤ/2` Decision Obstruction

`CyclicHolonomy` computed the first cohomology of the loop nerve with **real**
coefficients.  The same computation holds with coefficients in an **arbitrary
abelian group** `M`, and this generality is not idle: the obstruction carried by
a decision boundary is not a real number but a *label*, i.e. a class with
coefficients in `ZMod 2`.

Main results.

* `deltaLoop_of_sum_zero`, `isCoboundary_iff_holonomy_zero_M` — for any abelian
  group `M`, a cyclic `M`-valued overlap discrepancy glues iff its holonomy
  `∑ᵢ gᵢ` vanishes in `M`.
* `range_deltaLoopHom_eq_ker_holonomyHom`, `loopH1EquivCoeff` — hence
  `H¹(loop nerve, M) ≃+ M` for every abelian group `M`: the loop nerve carries
  exactly one independent obstruction, with values in the coefficient group.
* `parity_obstruction` — specialised to `M = ZMod 2`: a loop of regions across
  which the predicted label flips an **odd** number of times admits no globally
  consistent labelling.  This is the `ℤ/2` Čech class of an adversarial loop,
  the algebraic shadow of the sign holonomy of `CertifiedRadiusGluing`.
* `flip_pattern_nontrivial` — an explicit odd flip pattern (a single flip around
  the loop) realises the nontrivial class, so the `ZMod 2` cohomology is not
  merely abstractly nonzero but has an exhibited generator.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): "the loop obstruction is coefficient-agnostic; the
  robustness-relevant instance is `ZMod 2`, where the class is the parity of
  label flips around a loop of overlapping activation regions."
* Experiment (Experimenter): the real-coefficient proof transports verbatim once
  `ring`/`linarith` are replaced by `abel`; the only genuinely arithmetic step,
  the wrap-around index `n ↦ 0`, is group-theoretic and needs no field
  structure.  Surjectivity of the holonomy uses the indicator cochain
  `i ↦ if i = 0 then m else 0`.
* Analysis (Analyst): passing from `ℝ` to `ZMod 2` changes the *meaning* of the
  invariant from a magnitude to a parity, and the parity version is the one that
  is invariant under reparametrising the score; this explains why the metric
  defect theorem of `CyclicHolonomy` and the sign obstruction of
  `CertifiedRadiusGluing` are two faces of one class.
* Critique (Critic): `parity_obstruction` is not vacuous: `flip_pattern_nontrivial`
  exhibits an explicit cochain with holonomy `1`, and the theorem's conclusion is
  a strict non-existence statement.
* Synthesis (PI): `H¹(loop, M) ≃+ M` unifies the whole cycle: real coefficients
  give quantitative certificate defects, `ZMod 2` coefficients give qualitative
  adversarial label obstructions.
-/


open BigOperators Finset

open SheafCohomologyRobustness
open LoopCoefficients

variable {n : ℕ} {M : Type*} [AddCommGroup M]

/-! ## §1. The loop coboundary with coefficients in an abelian group -/





lemma partialSumM_full (g : Fin (n + 1) → M) : partialSumM g (n + 1) = ∑ j, g j := by
  unfold partialSumM
  congr 1
  ext j
  simpa using j.isLt



/-! ## §2. `H¹(loop, M) ≃+ M` -/






/-! ## §3. The `ZMod 2` parity obstruction on decision boundaries -/






open SheafCohomologyRobustness in
theorem solution(g : Fin (n + 1) → M) (hg : ∑ i, g i = 0) :
    deltaLoop (fun k => partialSumM g k.val) = g := by
  funext i
  simp only [deltaLoop]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
  · have hsucc : (i + 1 : Fin (n + 1)).val = i.val + 1 := by
      rw [Fin.val_add_one_of_lt]
      exact Fin.lt_def.mpr (by simpa using hi)
    rw [hsucc, partialSumM_succ g i.val i.isLt]
    abel
  · have hlast : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.val_add, ← hi]
    rw [hlast]
    have h0 : partialSumM g (0 : Fin (n + 1)).val = 0 := by simp [partialSumM]
    rw [h0, hi]
    have hkey := partialSumM_succ g n (by omega)
    rw [partialSumM_full, hg] at hkey
    have hin : (⟨n, by omega⟩ : Fin (n + 1)) = i := Fin.ext hi.symm
    rw [hin] at hkey
    have hgi : g i = - partialSumM g n := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hkey.symm
    rw [hgi]
    abel
