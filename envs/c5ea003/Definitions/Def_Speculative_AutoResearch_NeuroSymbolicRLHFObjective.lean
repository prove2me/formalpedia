-- Prove2me | Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
-- name    : Speculative_AutoResearch_NeuroSymbolicRLHFObjective
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:00.887503+00:00
-- url     : https://prove2.me/theorems/8a1a040e-3f1a-4da6-ba0d-96e3a4df09da
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_NeuroSymbolicRLHFObjective
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.NeuroSymbolicRLHFObjective`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean by skeleton subtraction
import Mathlib
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

namespace NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Basic definitions -/

/-- A finite probability vector: nonnegative and summing to one. -/
structure IsProb (p : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

/-- A strictly positive finite probability vector (full support). -/
structure IsPosProb (p : ι → ℝ) : Prop where
  pos : ∀ i, 0 < p i
  sum_one : ∑ i, p i = 1


/-- Finite Kullback–Leibler divergence, with the usual `0 log 0 = 0` convention
(automatic in Lean since `Real.log 0 = 0`). -/
def klDivFin (p q : ι → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- Partition function of the exponentially tilted (softmax) policy. -/
def tiltZ (β : ℝ) (ref r : ι → ℝ) : ℝ := ∑ i, ref i * Real.exp (r i / β)

/-- The exponentially tilted policy `ref(i) exp(r i / β) / Z`, i.e. the
"softmax over the reward" policy. -/
def gibbs (β : ℝ) (ref r : ι → ℝ) : ι → ℝ :=
  fun i => ref i * Real.exp (r i / β) / tiltZ β ref r

/-- The free energy `β log Z`, the optimal value of the RLHF objective. -/
def freeEnergy (β : ℝ) (ref r : ι → ℝ) : ℝ := β * Real.log (tiltZ β ref r)

/-- The RLHF objective: expected reward minus `β` times the KL penalty against
the SFT reference policy. -/
def rlhfObj (β : ℝ) (ref r p : ι → ℝ) : ℝ :=
  (∑ i, p i * r i) - β * klDivFin p ref

/-- The PTX (pre-training mix-in) term: `γ * 𝔼_{x ∼ pre}[log p x]`. -/
def ptxTerm (γ : ℝ) (pre p : ι → ℝ) : ℝ := γ * ∑ i, pre i * Real.log (p i)

/-- The full PPO-ptx objective of InstructGPT, rebranded neurosymbolically. -/
def rlhfPtxObj (β γ : ℝ) (ref r pre p : ι → ℝ) : ℝ :=
  rlhfObj β ref r p + ptxTerm γ pre p

/-! ## Level 0: Gibbs' inequality and its equality case -/





/-! ## Basic facts about the tilted policy -/





/-! ## Level 1: the exact three-point decomposition -/



/-! ## Level 2: the variational principle -/




/-! ## Level 3: quantitative alignment corollaries -/










/-! ## Level 4: tilting as a group action (algebra meets information geometry) -/








/-! ## Level 5: the pre-training mix-in (PTX) and the alignment tension -/








end NeuroSymbolicRLHF


