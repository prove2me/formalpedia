-- Prove2me | Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
-- name    : Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:49.375837+00:00
-- url     : https://prove2.me/theorems/1418014f-a2a1-402b-8afa-8e55e8fd699f
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_NeuroSymbolicRLHFRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.NeuroSymbolicRLHFRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
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

namespace NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Preference identifiability: Bradley–Terry data pins the reward down to a
constant -/

/-- Bradley–Terry probability that response `i` is preferred to response `j`
under reward `r`. -/
def btPref (r : ι → ℝ) (i j : ι) : ℝ := 1 / (1 + Real.exp (r j - r i))





/-! ## DPO reparametrisation -/

/-- The implicit ("DPO") reward attached to a policy `q` relative to the SFT
reference: `β log (q i / ref i)`. -/
def implicitReward (β : ℝ) (ref q : ι → ℝ) : ι → ℝ := fun i => β * Real.log (q i / ref i)



/-! ## Convex duality for the free energy -/






/-! ## No policy collapse: two-sided support bounds and `L¹` drift -/







end NeuroSymbolicRLHF


