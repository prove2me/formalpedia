-- Prove2me | solution 1 for SheafCohomologyRobustness.LoopCoefficients.partialSumM_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:40:43.955973+00:00
-- url     : https://prove2.me/submissions/5206837b-e34b-4f76-b3d6-c61ac1f2387f

-- Sol generated from MachineLearning/SheafCohomologyRobustness/LoopCoefficients.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_LoopCoefficients
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








/-! ## §2. `H¹(loop, M) ≃+ M` -/






/-! ## §3. The `ZMod 2` parity obstruction on decision boundaries -/






open SheafCohomologyRobustness in
theorem solution(g : Fin (n + 1) → M) (k : ℕ) (hk : k < n + 1) :
    partialSumM g (k + 1) = partialSumM g k + g ⟨k, hk⟩ := by
  unfold partialSumM
  have hins : (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k + 1))
      = insert (⟨k, hk⟩ : Fin (n + 1))
          (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · simp
      · omega
  have hnot : (⟨k, hk⟩ : Fin (n + 1))
      ∉ (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k)) := by simp
  rw [hins, Finset.sum_insert hnot]
  abel
