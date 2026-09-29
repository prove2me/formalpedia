-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_btPref_eq_iff
-- name    : NeuroSymbolicRLHF.btPref_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:43:31.862325+00:00
-- url     : https://prove2.me/theorems/774665ab-64e5-4b37-bec8-b7567958bdd2
-- title:
--   Two rewards induce the same Bradley–Terry preferences iff they differ by an
-- statement:
--   Two rewards induce the same Bradley–Terry preferences iff they differ by an
--   additive constant.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.btPref_eq_iff[Nonempty ι] {r s : ι → ℝ} :
--       (∀ i j, btPref r i j = btPref s i j) ↔ ∃ c : ℝ, ∀ i, r i = s i + c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean#L55

-- Thm stub generated from Speculative/AutoResearch/NeuroSymbolicRLHFRobustness.lean
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



omit [Fintype ι] in

theorem NeuroSymbolicRLHF.btPref_eq_iff[Nonempty ι] {r s : ι → ℝ} :
    (∀ i j, btPref r i j = btPref s i j) ↔ ∃ c : ℝ, ∀ i, r i = s i + c := by sorry
