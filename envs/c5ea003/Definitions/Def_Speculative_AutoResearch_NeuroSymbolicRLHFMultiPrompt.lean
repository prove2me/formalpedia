-- Prove2me | Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
-- name    : Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:39.161989+00:00
-- url     : https://prove2.me/theorems/d7dfdf60-ba08-4ae9-a54d-c458cb33aac1
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.NeuroSymbolicRLHFMultiPrompt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean by skeleton subtraction
import Mathlib
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

namespace NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## Part 1: prompt-wise decomposition of the RLHF objective -/

section MultiPrompt

variable {χ : Type*} [Fintype χ]

/-- The prompt-averaged RLHF objective `𝔼_{x ∼ D}[Objective(p x)]`. -/
def rlhfMulti (β : ℝ) (D : χ → ℝ) (ref r p : χ → ι → ℝ) : ℝ :=
  ∑ x, D x * rlhfObj β (ref x) (r x) (p x)

/-- The prompt-averaged optimal value. -/
def freeEnergyMulti (β : ℝ) (D : χ → ℝ) (ref r : χ → ι → ℝ) : ℝ :=
  ∑ x, D x * freeEnergy β (ref x) (r x)



/-- The complete PPO-ptx objective: prompt-averaged reward with KL penalty, plus
the pre-training mix-in coupled to the conditional policy at a distinguished
prompt `x₀`. -/
def fullPtxObj (β γ : ℝ) (D : χ → ℝ) (ref r : χ → ι → ℝ) (pre : ι → ℝ)
    (p : χ → ι → ℝ) (x₀ : χ) : ℝ :=
  rlhfMulti β D ref r p + ptxTerm γ pre (p x₀)



end MultiPrompt

/-! ## Part 2: uniqueness of the PPO-ptx optimum via strict concavity -/






end NeuroSymbolicRLHF


