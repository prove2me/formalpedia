-- Prove2me | solution 1 for NeuroSymbolicRLHF.klDivFin_midpoint_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:28:36.154389+00:00
-- url     : https://prove2.me/submissions/83ff1c34-3249-4d64-ae0c-74e9bea21b49

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
theorem solution{p q c : ι → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hc : IsPosProb c) (hne : p ≠ q) :
    klDivFin (fun i => (p i + q i) / 2) c < (klDivFin p c + klDivFin q c) / 2 := by
  have key : ∀ i : ι,
      ((p i + q i) / 2) * Real.log (((p i + q i) / 2) / c i)
        ≤ (p i * Real.log (p i / c i) + q i * Real.log (q i / c i)) / 2 := by
    intro i
    have hmid : (0:ℝ) ≤ (p i + q i) / 2 := by
      have := hp.nonneg i; have := hq.nonneg i; linarith
    rw [mul_log_div_eq hmid (hc.pos i), mul_log_div_eq (hp.nonneg i) (hc.pos i),
      mul_log_div_eq (hq.nonneg i) (hc.pos i)]
    have hconv := strictConvexOn_mul_log.convexOn.2 (mem_Ici.2 (hp.nonneg i))
      (mem_Ici.2 (hq.nonneg i)) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    simp only [smul_eq_mul] at hconv
    have harg : (1/2 : ℝ) * p i + (1/2 : ℝ) * q i = (p i + q i) / 2 := by ring
    rw [harg] at hconv
    linarith
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
    by_contra hall
    exact hne (funext fun i => not_not.1 fun h' => hall ⟨i, h'⟩)
  have keyj : ((p j + q j) / 2) * Real.log (((p j + q j) / 2) / c j)
      < (p j * Real.log (p j / c j) + q j * Real.log (q j / c j)) / 2 := by
    have hmid : (0:ℝ) ≤ (p j + q j) / 2 := by
      have := hp.nonneg j; have := hq.nonneg j; linarith
    rw [mul_log_div_eq hmid (hc.pos j), mul_log_div_eq (hp.nonneg j) (hc.pos j),
      mul_log_div_eq (hq.nonneg j) (hc.pos j)]
    have hconv := strictConvexOn_mul_log.2 (mem_Ici.2 (hp.nonneg j))
      (mem_Ici.2 (hq.nonneg j)) hj (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num)
    simp only [smul_eq_mul] at hconv
    have harg : (1/2 : ℝ) * p j + (1/2 : ℝ) * q j = (p j + q j) / 2 := by ring
    rw [harg] at hconv
    linarith
  have hlt : ∑ i, ((p i + q i) / 2) * Real.log (((p i + q i) / 2) / c i)
      < ∑ i, (p i * Real.log (p i / c i) + q i * Real.log (q i / c i)) / 2 :=
    Finset.sum_lt_sum (fun i _ => key i) ⟨j, Finset.mem_univ j, keyj⟩
  have hrhs : ∑ i, (p i * Real.log (p i / c i) + q i * Real.log (q i / c i)) / 2
      = (klDivFin p c + klDivFin q c) / 2 := by
    unfold klDivFin
    rw [← Finset.sum_add_distrib, ← Finset.sum_div]
  rw [klDivFin]
  linarith [hlt, hrhs]
