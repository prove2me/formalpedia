-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_tendsto_ref
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:24:06.432732+00:00
-- url     : https://prove2.me/submissions/9d427589-620c-4e74-919d-18c4495b6f92

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_l1_drift_le
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
theorem solution{m M : ℝ} {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hm : ∀ i, m ≤ r i) (hM : ∀ i, r i ≤ M) :
    Tendsto (fun β : ℝ => ∑ i, |gibbs β ref r i - ref i|) atTop (𝓝 0) := by
  have hquot : Tendsto (fun β : ℝ => (M - m) / β) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hexp : Tendsto (fun β : ℝ => Real.exp ((M - m) / β) - 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ => Real.exp ((M - m) / β)) atTop (𝓝 1) := by
      have h2 := (Real.continuous_exp.tendsto 0).comp hquot
      simpa using h2
    have h3 := h1.sub (tendsto_const_nhds (α := ℝ) (x := (1:ℝ)) (f := atTop))
    simpa using h3
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards with β
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    exact gibbs_l1_drift_le hβ href hm hM
