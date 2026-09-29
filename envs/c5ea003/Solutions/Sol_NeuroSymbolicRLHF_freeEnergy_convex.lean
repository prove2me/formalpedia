-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:12:33.771024+00:00
-- url     : https://prove2.me/submissions/aa51232a-1726-4f8b-a87b-d6a81ad344dc

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
import Theorems.Thm_NeuroSymbolicRLHF_IsPosProb_isProb
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_isPosProb
import Theorems.Thm_NeuroSymbolicRLHF_rlhfObj_gibbs
import Theorems.Thm_NeuroSymbolicRLHF_rlhfObj_le_freeEnergy
/-
Copyright (c) 2025. All rights reserved.

# Robustness, Preference Identifiability and Convex Duality for the RLHF Objective

Second research cycle, building directly on
`Catalog.Shared.NeuroSymbolicRLHFObjective` (variational principle, three-point
identity, torsor structure of exponential tilting).

Contents:

* **Preference identifiability (logistic ⋈ order theory).**  Bradley–Terry
  preference probabilities determine the reward *exactly up to an additive
  constant*, hence they determine the RLHF optimum uniquely: RLHF on preference
  data is a well-posed problem.
* **DPO reparametrisation.**  The map `reward ↦ optimal policy` is a bijection
  between rewards modulo constants and full-support policies; the inverse is the
  implicit reward `β log(π/π_SFT)`.
* **Convex duality.**  The free energy is convex, monotone and `1`-Lipschitz for
  the sup-norm in the reward, all obtained from the variational principle
  (a supremum of affine functionals).
* **Reward-model misspecification ("reward hacking") bound.**  If the learned
  reward is uniformly `ε`-close to the true reward, the policy it produces loses
  at most `2ε` of true regularised value.  The factor `2` is structural.
* **No policy collapse.**  Pointwise two-sided bounds
  `π_SFT(i) e^{-(M-m)/β} ≤ π*(i) ≤ π_SFT(i) e^{(M-m)/β)}`, an `L¹` drift bound
  `‖π* - π_SFT‖₁ ≤ e^{(M-m)/β} - 1`, and the limit `π* → π_SFT` as `β → ∞`.

Every theorem is proved; no `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Filter Topology

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Preference identifiability: Bradley–Terry data pins the reward down to a
constant -/






/-! ## DPO reparametrisation -/




/-! ## Convex duality for the free energy -/






/-! ## No policy collapse: two-sided support bounds and `L¹` drift -/








open NeuroSymbolicRLHF in
theorem solution{β lam : ℝ} (hβ : 0 < β) {ref r s : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    freeEnergy β ref (fun i => lam * r i + (1 - lam) * s i)
      ≤ lam * freeEnergy β ref r + (1 - lam) * freeEnergy β ref s := by
  set t : ι → ℝ := fun i => lam * r i + (1 - lam) * s i with ht
  set p := gibbs β ref t with hp
  have hpp : IsPosProb p := gibbs_isPosProb href
  have hmix : ∑ i, p i * t i = lam * (∑ i, p i * r i) + (1 - lam) * ∑ i, p i * s i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [ht]; ring
  have hopt := rlhfObj_gibbs (β := β) (r := t) hβ href
  have hr := rlhfObj_le_freeEnergy (β := β) (r := r) (p := p) hβ href hpp.isProb
  have hs := rlhfObj_le_freeEnergy (β := β) (r := s) (p := p) hβ href hpp.isProb
  unfold rlhfObj at hopt hr hs
  rw [hmix] at hopt
  nlinarith [hr, hs, hopt, h0, sub_nonneg.2 h1]
