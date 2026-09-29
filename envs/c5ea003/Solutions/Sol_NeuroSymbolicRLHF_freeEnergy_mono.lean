-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_mono
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:26:30.403295+00:00
-- url     : https://prove2.me/submissions/67afcdee-67a1-41fd-9df7-45dd20d5e9f4

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos

open Finset Real BigOperators
open NeuroSymbolicRLHF

set_option autoImplicit false

/- Ported from paulklemstine/Lean, commit 53c2925a02,
   Catalog/Speculative/AutoResearch/RLHFHilbertIsometry.lean. -/
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℝ} (hβ : 0 < β) {ref r₁ r₂ : ι → ℝ} (href : IsPosProb ref)
    (h : ∀ i, r₁ i ≤ r₂ i) : freeEnergy β ref r₁ ≤ freeEnergy β ref r₂ := by
  classical
  have hZ : tiltZ β ref r₁ ≤ tiltZ β ref r₂ := by
    refine Finset.sum_le_sum fun i _ => ?_
    have : Real.exp (r₁ i / β) ≤ Real.exp (r₂ i / β) :=
      Real.exp_le_exp.mpr (by gcongr; exact h i)
    exact mul_le_mul_of_nonneg_left this (href.pos i).le
  have h1 : 0 < tiltZ β ref r₁ := tiltZ_pos href
  simp only [freeEnergy]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log h1 hZ) hβ.le
