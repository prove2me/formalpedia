-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_le_ref_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:21:11.561212+00:00
-- url     : https://prove2.me/submissions/d4a226c0-5d29-4ec7-8358-ebee3838060b

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
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


theorem le_tiltZ_of_le {β m : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hm : ∀ i, m ≤ r i) :
    Real.exp (m / β) ≤ tiltZ β ref r := by
  unfold tiltZ
  calc Real.exp (m / β) = ∑ i, ref i * Real.exp (m / β) := by
        rw [← Finset.sum_mul, href.sum_one, one_mul]
    _ ≤ ∑ i, ref i * Real.exp (r i / β) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hβ).2 (hm i))) (href.pos i).le






open NeuroSymbolicRLHF in
theorem solution{β m M : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hm : ∀ i, m ≤ r i) (hM : ∀ i, r i ≤ M) (i : ι) :
    gibbs β ref r i ≤ ref i * Real.exp ((M - m) / β) := by
  have hZ : 0 < tiltZ β ref r := tiltZ_pos href
  have hZge : Real.exp (m / β) ≤ tiltZ β ref r := le_tiltZ_of_le hβ href hm
  have hexp : Real.exp (r i / β) ≤ Real.exp (M / β) :=
    Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right hβ).2 (hM i))
  have hkey : ref i * Real.exp (r i / β)
      ≤ ref i * Real.exp ((M - m) / β) * tiltZ β ref r := by
    have h1 : ref i * Real.exp ((M - m) / β) * Real.exp (m / β)
        ≤ ref i * Real.exp ((M - m) / β) * tiltZ β ref r :=
      mul_le_mul_of_nonneg_left hZge (mul_pos (href.pos i) (Real.exp_pos _)).le
    have h2 : ref i * Real.exp ((M - m) / β) * Real.exp (m / β)
        = ref i * Real.exp (M / β) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have h3 : ref i * Real.exp (r i / β) ≤ ref i * Real.exp (M / β) :=
      mul_le_mul_of_nonneg_left hexp (href.pos i).le
    linarith [h1, h2 ▸ h1, h3]
  unfold gibbs
  rw [div_le_iff₀ hZ]
  exact hkey
