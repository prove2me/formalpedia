-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_klDivFin_midpoint_lt
-- name    : NeuroSymbolicRLHF.klDivFin_midpoint_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:48:49.166401+00:00
-- url     : https://prove2.me/theorems/b40ec368-07f2-4586-9fc9-dd1ae0b98717
-- title:
--   Strict convexity of the KL divergence in its first argument, in midpoint
-- statement:
--   Strict convexity of the KL divergence in its first argument, in midpoint
--   form: if `p ≠ q` then the KL divergence of the midpoint is strictly below the
--   average.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.klDivFin_midpoint_lt{p q c : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
--       (hc : IsPosProb c) (hne : p ≠ q) :
--       klDivFin (fun i => (p i + q i) / 2) c < (klDivFin p c + klDivFin q c) / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean#L148

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









/-! ## Part 2: uniqueness of the PPO-ptx optimum via strict concavity -/

theorem NeuroSymbolicRLHF.klDivFin_midpoint_lt{p q c : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hc : IsPosProb c) (hne : p ≠ q) :
    klDivFin (fun i => (p i + q i) / 2) c < (klDivFin p c + klDivFin q c) / 2 := by sorry
