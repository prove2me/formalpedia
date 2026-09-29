-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_transitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:24:07.995915+00:00
-- url     : https://prove2.me/submissions/0ff79b09-2280-469e-b713-c04ef3a10cc3

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
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
theorem solution{β : ℝ} (hβ : 0 < β) {p q : ι → ℝ} [Nonempty ι]
    (hp : IsPosProb p) (hq : IsPosProb q) :
    gibbs β p (fun i => β * Real.log (q i / p i)) = q := by
  have hterm : ∀ i : ι, p i * Real.exp (β * Real.log (q i / p i) / β) = q i := by
    intro i
    have hb : β * Real.log (q i / p i) / β = Real.log (q i / p i) := by
      field_simp
    rw [hb, Real.exp_log (div_pos (hq.pos i) (hp.pos i)), mul_comm,
      div_mul_eq_mul_div, mul_div_assoc, div_self (hp.pos i).ne', mul_one]
  have hZ : tiltZ β p (fun i => β * Real.log (q i / p i)) = 1 := by
    unfold tiltZ
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact hq.sum_one
  funext i
  show p i * Real.exp (β * Real.log (q i / p i) / β)
      / tiltZ β p (fun i => β * Real.log (q i / p i)) = q i
  rw [hZ, hterm i, div_one]
