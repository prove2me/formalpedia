-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_fullPtxObj_eq_iff
-- name    : NeuroSymbolicRLHF.fullPtxObj_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:46:47.918456+00:00
-- url     : https://prove2.me/theorems/97c8fabf-4b8d-4a38-a84c-e3e29988fc4e
-- title:
--   Localisation of the alignment tax: the joint bound for the full
-- statement:
--   **Localisation of the alignment tax**: the joint bound for the full
--   objective is attainable iff the pre-training distribution is *exactly* the
--   tilted policy at the coupled prompt `x₀`; the conditionals at all other prompts
--   are unaffected by the PTX term.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.fullPtxObj_eq_iff{β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) {D : χ → ℝ}
--       {ref r : χ → ι → ℝ} {pre : ι → ℝ} {p : χ → ι → ℝ} {x₀ : χ} [Nonempty ι]
--       (hD : ∀ x, 0 < D x) (href : ∀ x, IsPosProb (ref x)) (hpre : IsPosProb pre)
--       (hp : ∀ x, IsPosProb (p x)) :
--       fullPtxObj β γ D ref r pre p x₀ = freeEnergyMulti β D ref r + ptxTerm γ pre pre
--         ↔ (∀ x, p x = gibbs β (ref x) (r x)) ∧ pre = p x₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean#L99

-- Thm stub generated from Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
/-
Copyright (c) 2025. All rights reserved.

# Multi-Prompt RLHF and Uniqueness of the PPO-ptx Optimum

Third research cycle, building on
`Catalog.Shared.NeuroSymbolicRLHFObjective`.

Two results:

* **Prompt-wise decomposition.**  The full InstructGPT objective takes an
  expectation over a prompt distribution `D`.  We show that the optimum
  decomposes: the global optimum of the prompt-averaged objective is attained
  exactly when *every* conditional policy is the exponentially tilted policy for
  its own prompt (assuming every prompt has positive probability), and the
  optimal value is the `D`-average of the per-prompt free energies.
  Consequently the **alignment tax of the PTX term is localised**: coupling the
  pre-training mix-in to a single prompt `x₀` leaves the optimal conditional
  policies at all other prompts untouched, and the joint bound is attainable
  iff the pre-training distribution equals the tilted policy at `x₀`.

* **Uniqueness of the PPO-ptx optimum.**  The full objective (reward + KL
  penalty + PTX) has *at most one* maximiser among full-support policies.  This
  is proved from strict convexity of `x ↦ x log x` (strict convexity of the KL
  divergence in its first argument) together with concavity of `log`
  (convexity of the KL divergence in its second argument); no differentiability
  or first-order conditions are used.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Set

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Part 1: prompt-wise decomposition of the RLHF objective -/


variable {χ : Type*} [Fintype χ]

theorem NeuroSymbolicRLHF.fullPtxObj_eq_iff{β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) {D : χ → ℝ}
    {ref r : χ → ι → ℝ} {pre : ι → ℝ} {p : χ → ι → ℝ} {x₀ : χ} [Nonempty ι]
    (hD : ∀ x, 0 < D x) (href : ∀ x, IsPosProb (ref x)) (hpre : IsPosProb pre)
    (hp : ∀ x, IsPosProb (p x)) :
    fullPtxObj β γ D ref r pre p x₀ = freeEnergyMulti β D ref r + ptxTerm γ pre pre
      ↔ (∀ x, p x = gibbs β (ref x) (r x)) ∧ pre = p x₀ := by sorry
