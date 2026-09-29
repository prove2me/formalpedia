-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhfPtx_maximizer_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:48.093919+00:00
-- url     : https://prove2.me/submissions/3e26fa15-5d5a-4771-b299-e47a1bde6061

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_IsPosProb_isProb
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_isPosProb
import Theorems.Thm_NeuroSymbolicRLHF_klDivFin_midpoint_le_snd
import Theorems.Thm_NeuroSymbolicRLHF_klDivFin_midpoint_lt
import Theorems.Thm_NeuroSymbolicRLHF_rlhfPtxObj_eq
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




theorem isPosProb_midpoint {p q : ι → ℝ} (hp : IsPosProb p) (hq : IsPosProb q) :
    IsPosProb (fun i => (p i + q i) / 2) := by
  refine ⟨fun i => by have := hp.pos i; have := hq.pos i; linarith, ?_⟩
  have : ∑ i, (p i + q i) / 2 = (∑ i, p i + ∑ i, q i) / 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_div]
  rw [this, hp.sum_one, hq.sum_one]
  norm_num



open NeuroSymbolicRLHF in
theorem solution{β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    {ref r pre p q : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hpre : IsPosProb pre) (hp : IsPosProb p) (hq : IsPosProb q)
    (hpmax : ∀ z : ι → ℝ, IsPosProb z →
      rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre p)
    (hqmax : ∀ z : ι → ℝ, IsPosProb z →
      rlhfPtxObj β γ ref r pre z ≤ rlhfPtxObj β γ ref r pre q) :
    p = q := by
  by_contra hne
  set m : ι → ℝ := fun i => (p i + q i) / 2 with hm
  have hmm : IsPosProb m := isPosProb_midpoint hp hq
  have hpq : rlhfPtxObj β γ ref r pre p = rlhfPtxObj β γ ref r pre q :=
    le_antisymm (hqmax p hp) (hpmax q hq)
  have hklfst : klDivFin m (gibbs β ref r)
      < (klDivFin p (gibbs β ref r) + klDivFin q (gibbs β ref r)) / 2 :=
    klDivFin_midpoint_lt hp.isProb hq.isProb (gibbs_isPosProb href) hne
  have hklsnd : klDivFin pre m ≤ (klDivFin pre p + klDivFin pre q) / 2 :=
    klDivFin_midpoint_le_snd hpre.isProb hp hq
  have hep := rlhfPtxObj_eq hβ href hpre hp (r := r) (γ := γ)
  have heq := rlhfPtxObj_eq hβ href hpre hq (r := r) (γ := γ)
  have hem := rlhfPtxObj_eq hβ href hpre hmm (r := r) (γ := γ)
  have hmle : rlhfPtxObj β γ ref r pre m ≤ rlhfPtxObj β γ ref r pre p := hpmax m hmm
  rw [hep, heq] at hpq
  rw [hem, hep] at hmle
  nlinarith [hklfst, hklsnd, hβ, hγ]
