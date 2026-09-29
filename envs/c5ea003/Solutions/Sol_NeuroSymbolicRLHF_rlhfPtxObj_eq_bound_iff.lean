-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhfPtxObj_eq_bound_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:47.342667+00:00
-- url     : https://prove2.me/submissions/29d8aa67-0923-4dc1-8b0f-bd8b0b0b57de

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_IsPosProb_isProb
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_isPosProb
import Theorems.Thm_NeuroSymbolicRLHF_klDivFin_eq_zero_iff
import Theorems.Thm_NeuroSymbolicRLHF_klDivFin_nonneg
import Theorems.Thm_NeuroSymbolicRLHF_rlhfPtxObj_eq
/-
Copyright (c) 2025. All rights reserved.

# The Neurosymbolic RLHF Objective: a Variational / Torsor-Theoretic Analysis

## Overview

This file gives a complete, `sorry`-free formal analysis of the KL-regularised
reinforcement-learning objective used by RLHF (InstructGPT / PPO-ptx style):

  `Objective(p) = 𝔼_p[RM] - β * KL(p ‖ p_SFT) + γ * 𝔼_{x∼D_pre}[log p x]`

over a finite response space `ι`.

The mathematical content is organised as a strict hierarchy:

* **Level 0 (information theory).**  Gibbs' inequality for the finite
  Kullback–Leibler divergence, together with its *equality case*.
* **Level 1 (exact decomposition).**  The *three-point identity*
  `Objective β r ref p = freeEnergy β ref r - β * KL(p ‖ gibbs β ref r)`.
  Every optimality statement below is a corollary of this single identity.
* **Level 2 (variational principle).**  The Donsker–Varadhan / Gibbs
  variational principle: the KL-regularised optimum is the exponentially tilted
  ("softmax") policy, the optimal value is the free energy `β log Z`, and the
  maximiser is *unique*.
* **Level 3 (quantitative alignment corollaries).**  Sandwich
  `𝔼_ref[r] ≤ β log Z ≤ max r`, monotonicity of the optimal value in the
  KL-coefficient β, the drift bound `KL(π* ‖ ref) ≤ (max r - min r)/β`, and the
  fact that tilting never decreases expected reward.
* **Level 4 (algebra ⋈ information geometry).**  Exponential tilting is an
  *additive group action* of the reward space `(ι → ℝ, +)` on the open simplex,
  it is transitive, and its stabiliser is exactly the constant rewards.  Hence
  the open simplex is a torsor under `(ι → ℝ)/ℝ·1`, and *sequential RLHF with
  rewards `r₁` then `r₂` equals single-stage RLHF with reward `r₁ + r₂`*.
* **Level 5 (PTX).**  The pre-training mix-in term is bounded by the negative
  entropy of the pre-training distribution, and the two upper bounds (reward+KL
  and PTX) are *simultaneously attainable if and only if* the pre-training
  distribution coincides with the tilted policy — an exact obstruction theorem
  for the reward/PTX tension.

All results are proved from scratch; no `sorry`, no `native_decide`.
-/

open Finset Real BigOperators

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Basic definitions -/











/-! ## Level 0: Gibbs' inequality and its equality case -/





/-! ## Basic facts about the tilted policy -/





/-! ## Level 1: the exact three-point decomposition -/



/-! ## Level 2: the variational principle -/




/-! ## Level 3: quantitative alignment corollaries -/

theorem klDivFin_self {p : ι → ℝ} (hp : IsPosProb p) : klDivFin p p = 0 :=
  (klDivFin_eq_zero_iff hp.isProb hp).2 rfl









/-! ## Level 4: tilting as a group action (algebra meets information geometry) -/








/-! ## Level 5: the pre-training mix-in (PTX) and the alignment tension -/









open NeuroSymbolicRLHF in
theorem solution{β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) {ref r pre p : ι → ℝ}
    [Nonempty ι] (href : IsPosProb ref) (hpre : IsPosProb pre) (hp : IsPosProb p) :
    rlhfPtxObj β γ ref r pre p = freeEnergy β ref r + ptxTerm γ pre pre
      ↔ p = gibbs β ref r ∧ pre = p := by
  have h1 : 0 ≤ klDivFin p (gibbs β ref r) :=
    klDivFin_nonneg hp.isProb (gibbs_isPosProb href)
  have h2 : 0 ≤ klDivFin pre p := klDivFin_nonneg hpre.isProb hp
  rw [rlhfPtxObj_eq hβ href hpre hp]
  constructor
  · intro h
    have hz1 : klDivFin p (gibbs β ref r) = 0 := by nlinarith
    have hz2 : klDivFin pre p = 0 := by nlinarith
    exact ⟨(klDivFin_eq_zero_iff hp.isProb (gibbs_isPosProb href)).1 hz1,
      (klDivFin_eq_zero_iff hpre.isProb hp).1 hz2⟩
  · rintro ⟨rfl, rfl⟩
    rw [klDivFin_self hp]
    ring
