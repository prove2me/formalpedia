-- Prove2me | solution 1 for NeuroSymbolicRLHF.klDivFin_midpoint_le_snd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:28:35.669934+00:00
-- url     : https://prove2.me/submissions/54e7f577-e6a7-437a-9af5-c25187268ffb

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFMultiPrompt.lean
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

/-- Rewriting a KL summand, valid also at `a = 0`. -/
theorem mul_log_div_eq {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    a * Real.log (a / c) = a * Real.log a - a * Real.log c := by
  rcases eq_or_lt_of_le ha with h | h
  · simp [← h]
  · rw [Real.log_div h.ne' hc.ne']
    ring






open NeuroSymbolicRLHF in
theorem solution{a p q : ι → ℝ} (ha : IsProb a) (hp : IsPosProb p)
    (hq : IsPosProb q) :
    klDivFin a (fun i => (p i + q i) / 2) ≤ (klDivFin a p + klDivFin a q) / 2 := by
  have key : ∀ i : ι,
      a i * Real.log (a i / ((p i + q i) / 2))
        ≤ (a i * Real.log (a i / p i) + a i * Real.log (a i / q i)) / 2 := by
    intro i
    have hmid : (0:ℝ) < (p i + q i) / 2 := by
      have := hp.pos i; have := hq.pos i; linarith
    rw [mul_log_div_eq (ha.nonneg i) hmid, mul_log_div_eq (ha.nonneg i) (hp.pos i),
      mul_log_div_eq (ha.nonneg i) (hq.pos i)]
    have hlog : (Real.log (p i) + Real.log (q i)) / 2 ≤ Real.log ((p i + q i) / 2) := by
      have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 (hp.pos i))
        (mem_Ioi.2 (hq.pos i)) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num)
      simp only [smul_eq_mul] at hconc
      have harg : (1/2 : ℝ) * p i + (1/2 : ℝ) * q i = (p i + q i) / 2 := by ring
      rw [harg] at hconc
      linarith
    nlinarith [ha.nonneg i, hlog]
  calc klDivFin a (fun i => (p i + q i) / 2)
      ≤ ∑ i, (a i * Real.log (a i / p i) + a i * Real.log (a i / q i)) / 2 :=
        Finset.sum_le_sum fun i _ => key i
    _ = (klDivFin a p + klDivFin a q) / 2 := by
        unfold klDivFin
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]
