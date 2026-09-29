-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_rlhfPtx_maximizer_unique
-- name    : NeuroSymbolicRLHF.rlhfPtx_maximizer_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:49:36.050309+00:00
-- url     : https://prove2.me/theorems/3c27d436-e9a1-4333-90cd-df433a3dd6ff
-- title:
--   Uniqueness of the PPO-ptx optimum: the full objective (reward, KL
-- statement:
--   **Uniqueness of the PPO-ptx optimum**: the full objective (reward, KL
--   penalty and pre-training mix-in) has at most one maximiser among full-support
--   policies.  Strict concavity comes from the KL term alone, so the statement holds
--   for every `γ ≥ 0`, including the pure RLHF case `γ = 0`.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.rlhfPtx_maximizer_unique{β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
--       {ref r pre p q : ι → ℝ} [Nonempty ι]
--       (href : IsPosProb ref) (hpre : IsPosProb pre) (hp : IsPosProb p) (hq : IsPosProb q)
--       (hpmax : ∀ z : ι → ℝ, IsPosProb z →
--         rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre p)
--       (hqmax : ∀ z : ι → ℝ, IsPosProb z →
--         rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre q) :
--       p = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean#L231

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

theorem NeuroSymbolicRLHF.rlhfPtx_maximizer_unique{β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    {ref r pre p q : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hpre : IsPosProb pre) (hp : IsPosProb p) (hq : IsPosProb q)
    (hpmax : ∀ z : ι → ℝ, IsPosProb z →
      rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre p)
    (hqmax : ∀ z : ι → ℝ, IsPosProb z →
      rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre q) :
    p = q := by sorry
