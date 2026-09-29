-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_kl_drift_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:21:11.045326+00:00
-- url     : https://prove2.me/submissions/49f99370-7665-4246-bb56-93f6f8a4f63b

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_IsPosProb_isProb
import Theorems.Thm_NeuroSymbolicRLHF_expected_ref_le_freeEnergy
import Theorems.Thm_NeuroSymbolicRLHF_freeEnergy_le_of_le
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_isPosProb
import Theorems.Thm_NeuroSymbolicRLHF_le_expectation
import Theorems.Thm_NeuroSymbolicRLHF_rlhfObj_gibbs
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


/-- Expectations of a bounded reward under a probability vector are bounded. -/
theorem expectation_le {p r : ι → ℝ} {M : ℝ} (hp : IsProb p) (hM : ∀ i, r i ≤ M) :
    ∑ i, p i * r i ≤ M := by
  calc ∑ i, p i * r i ≤ ∑ i, p i * M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp.nonneg i)
    _ = M := by rw [← Finset.sum_mul, hp.sum_one, one_mul]




/-- **Sandwich**: the optimal RLHF value lies between the reference reward and
the maximal reward. -/
theorem freeEnergy_mem_Icc {β m M : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hm : ∀ i, m ≤ r i) (hM : ∀ i, r i ≤ M) :
    m ≤ freeEnergy β ref r ∧ freeEnergy β ref r ≤ M :=
  ⟨le_trans (le_expectation href.isProb hm) (expected_ref_le_freeEnergy hβ href),
    freeEnergy_le_of_le hβ href hM⟩




/-! ## Level 4: tilting as a group action (algebra meets information geometry) -/








/-! ## Level 5: the pre-training mix-in (PTX) and the alignment tension -/









open NeuroSymbolicRLHF in
theorem solution{β m M : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hm : ∀ i, m ≤ r i) (hM : ∀ i, r i ≤ M) :
    β * klDivFin (gibbs β ref r) ref ≤ M - m := by
  have hg : IsPosProb (gibbs β ref r) := gibbs_isPosProb href
  have h := rlhfObj_gibbs (β := β) (r := r) hβ href
  have hsum : ∑ i, gibbs β ref r i * r i ≤ M := expectation_le hg.isProb hM
  have hlow : m ≤ freeEnergy β ref r := (freeEnergy_mem_Icc hβ href hm hM).1
  unfold rlhfObj at h
  linarith
