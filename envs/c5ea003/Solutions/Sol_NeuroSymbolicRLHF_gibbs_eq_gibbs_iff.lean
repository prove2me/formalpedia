-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_eq_gibbs_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:18:56.711663+00:00
-- url     : https://prove2.me/submissions/ec69ba0f-d25b-4fbc-bfff-aa1b0bdca5e6

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_add_const
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
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
theorem solution{β : ℝ} (hβ : 0 < β) {ref r s : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) :
    gibbs β ref r = gibbs β ref s ↔ ∃ c : ℝ, ∀ i, r i = s i + c := by
  have hZr : 0 < tiltZ β ref r := tiltZ_pos href
  have hZs : 0 < tiltZ β ref s := tiltZ_pos href
  constructor
  · intro h
    refine ⟨β * Real.log (tiltZ β ref r / tiltZ β ref s), fun i => ?_⟩
    have hi : ref i * Real.exp (r i / β) / tiltZ β ref r
        = ref i * Real.exp (s i / β) / tiltZ β ref s := congrFun h i
    have hrefi := href.pos i
    have he1 := Real.exp_pos (r i / β)
    have he2 := Real.exp_pos (s i / β)
    have hi2 : Real.exp (r i / β) * tiltZ β ref s
        = Real.exp (s i / β) * tiltZ β ref r := by
      field_simp at hi
      nlinarith [hi]
    have hdiv : Real.exp (r i / β - s i / β) = tiltZ β ref r / tiltZ β ref s := by
      rw [Real.exp_sub, div_eq_div_iff (by positivity) hZs.ne']
      nlinarith [hi2]
    have hlog : r i / β - s i / β = Real.log (tiltZ β ref r / tiltZ β ref s) := by
      rw [← hdiv, Real.log_exp]
    have hβ' : β ≠ 0 := hβ.ne'
    field_simp at hlog
    field_simp
    linarith [hlog]
  · rintro ⟨c, hc⟩
    have hrs : r = fun i => s i + c := funext hc
    rw [hrs, gibbs_add_const c href]
