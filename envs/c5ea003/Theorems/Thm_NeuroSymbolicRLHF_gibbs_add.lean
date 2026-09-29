-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_gibbs_add
-- name    : NeuroSymbolicRLHF.gibbs_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:46:48.354822+00:00
-- url     : https://prove2.me/theorems/6860e37d-aae6-47cc-85ed-9f77c81bde95
-- title:
--   Additivity of tilting: tilting by `r` and then by `s` is tilting by
-- statement:
--   **Additivity of tilting**: tilting by `r` and then by `s` is tilting by
--   `r + s`.  Exponential tilting is an action of the additive group of rewards on
--   the open simplex.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.gibbs_add{β : ℝ} {ref r s : ι → ℝ} [Nonempty ι] (href : IsPosProb ref) :
--       gibbs β (gibbs β ref r) s = gibbs β ref (fun i => r i + s i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean#L391

-- Thm stub generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean
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

theorem NeuroSymbolicRLHF.gibbs_add{β : ℝ} {ref r s : ι → ℝ} [Nonempty ι] (href : IsPosProb ref) :
    gibbs β (gibbs β ref r) s = gibbs β ref (fun i => r i + s i) := by sorry
