-- Prove2me | solution 1 for NeuroSymbolicRLHF.btPref_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:47:53.427367+00:00
-- url     : https://prove2.me/submissions/1698ba55-5703-4328-bb2d-16959a108532

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
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
omit [Fintype ι] in
theorem solution[Nonempty ι] {r s : ι → ℝ} :
    (∀ i j, btPref r i j = btPref s i j) ↔ ∃ c : ℝ, ∀ i, r i = s i + c := by
  constructor
  · intro h
    obtain ⟨j0⟩ := ‹Nonempty ι›
    refine ⟨r j0 - s j0, fun i => ?_⟩
    have hij := h i j0
    unfold btPref at hij
    have hpos1 : (0:ℝ) < 1 + Real.exp (r j0 - r i) := by positivity
    have hpos2 : (0:ℝ) < 1 + Real.exp (s j0 - s i) := by positivity
    have hexp : Real.exp (r j0 - r i) = Real.exp (s j0 - s i) := by
      field_simp at hij
      linarith
    have := Real.exp_injective hexp
    linarith
  · rintro ⟨c, hc⟩ i j
    unfold btPref
    rw [hc i, hc j]
    ring_nf
