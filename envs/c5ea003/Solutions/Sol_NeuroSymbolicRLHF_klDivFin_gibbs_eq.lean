-- Prove2me | solution 1 for NeuroSymbolicRLHF.klDivFin_gibbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:04:46.656748+00:00
-- url     : https://prove2.me/submissions/8fab9d39-a95a-4560-94ce-a6ca0923be63

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_pos
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
theorem solution{β : ℝ} {ref r p : ι → ℝ}
    [Nonempty ι] (href : IsPosProb ref) (hp : IsProb p) :
    klDivFin p (gibbs β ref r)
      = klDivFin p ref - (∑ i, p i * r i) / β + Real.log (tiltZ β ref r) := by
  have hZ : 0 < tiltZ β ref r := tiltZ_pos href
  have hterm : ∀ i : ι,
      p i * Real.log (p i / gibbs β ref r i)
        = p i * Real.log (p i / ref i) - p i * (r i / β) + p i * Real.log (tiltZ β ref r) := by
    intro i
    rcases eq_or_lt_of_le (hp.nonneg i) with h | h
    · simp [← h]
    · have hgpos : 0 < gibbs β ref r i := gibbs_pos href i
      have hg : gibbs β ref r i = ref i * Real.exp (r i / β) / tiltZ β ref r := rfl
      have hnum : (0:ℝ) < ref i * Real.exp (r i / β) :=
        mul_pos (href.pos i) (Real.exp_pos _)
      have h1 : Real.log (p i / gibbs β ref r i)
          = Real.log (p i) - Real.log (ref i) - r i / β + Real.log (tiltZ β ref r) := by
        rw [hg, Real.log_div h.ne' (by positivity),
          Real.log_div hnum.ne' hZ.ne', Real.log_mul (href.pos i).ne'
            (Real.exp_ne_zero _), Real.log_exp]
        ring
      rw [h1, Real.log_div h.ne' (href.pos i).ne']
      ring
  have hr : ∑ i, p i * (r i / β) = (∑ i, p i * r i) / β := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc klDivFin p (gibbs β ref r)
      = ∑ i, (p i * Real.log (p i / ref i) - p i * (r i / β)
          + p i * Real.log (tiltZ β ref r)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = klDivFin p ref - (∑ i, p i * r i) / β + Real.log (tiltZ β ref r) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hr,
          hp.sum_one, one_mul]
        rfl
