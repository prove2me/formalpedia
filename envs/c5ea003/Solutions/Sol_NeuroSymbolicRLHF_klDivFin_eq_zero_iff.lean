-- Prove2me | solution 1 for NeuroSymbolicRLHF.klDivFin_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:04:46.17597+00:00
-- url     : https://prove2.me/submissions/1839e974-13d4-4a72-ab97-9bb3bd2236c1

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_term_le
import Theorems.Thm_NeuroSymbolicRLHF_term_lt
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










/-! ## Level 4: tilting as a group action (algebra meets information geometry) -/








/-! ## Level 5: the pre-training mix-in (PTX) and the alignment tension -/









open NeuroSymbolicRLHF in
theorem solution{p q : ι → ℝ} (hp : IsProb p) (hq : IsPosProb q) :
    klDivFin p q = 0 ↔ p = q := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
      by_contra hall
      exact hne (funext fun i => not_not.1 (fun h' => hall ⟨i, h'⟩))
    have hlt : ∑ i, (p i - q i) < ∑ i, p i * Real.log (p i / q i) := by
      refine Finset.sum_lt_sum (fun i _ => term_le (p i) (q i) (hp.nonneg i) (hq.pos i))
        ⟨j, Finset.mem_univ j, term_lt (p j) (q j) (hp.nonneg j) (hq.pos j) hj⟩
    have hz : ∑ i : ι, (p i - q i) = 0 := by
      rw [Finset.sum_sub_distrib, hp.sum_one, hq.sum_one, sub_self]
    rw [hz, ← klDivFin] at hlt
    linarith
  · rintro rfl
    unfold klDivFin
    have : ∀ i : ι, p i * Real.log (p i / p i) = 0 := by
      intro i
      rw [div_self (hq.pos i).ne']
      simp
    exact Finset.sum_eq_zero fun i _ => this i
