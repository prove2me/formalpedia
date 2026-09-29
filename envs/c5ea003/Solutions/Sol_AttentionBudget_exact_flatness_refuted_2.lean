-- Prove2me | solution 2 for AttentionBudget.exact_flatness_refuted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:11:06.908983+00:00
-- url     : https://prove2.me/submissions/20a8fec8-b34b-4e07-a80a-e967b3aca275

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Definitions.Def_Shared_AttentionBudgetScaling
open AttentionBudget in
theorem solution :
    kstar (fun i => (1 / 2 : ℝ) ^ i) 1 (3 / 4) = 1 ∧
      kstar (fun i => (1 / 2 : ℝ) ^ i) 2 (3 / 4) = 2 := by
  constructor
  · -- one key already carries all of a length-1 context
    have hm : (3 / 4 : ℝ) ≤ retained (fun i => (1 / 2 : ℝ) ^ i) 1 1 := by
      simp [retained, headMass]
      norm_num
    unfold kstar
    apply le_antisymm (Nat.sInf_le hm)
    apply le_csInf ⟨1, hm⟩
    intro k hk
    by_contra h
    push_neg at h
    interval_cases k
    simp [retained, headMass] at hk
    norm_num at hk
  · -- at length 2 one key keeps only `1 / (3/2) = 2/3 < 3/4`
    have hm : (3 / 4 : ℝ) ≤ retained (fun i => (1 / 2 : ℝ) ^ i) 2 2 := by
      simp [retained, headMass]
      norm_num
    unfold kstar
    apply le_antisymm (Nat.sInf_le hm)
    apply le_csInf ⟨2, hm⟩
    intro k hk
    by_contra h
    push_neg at h
    interval_cases k
    · simp [retained, headMass] at hk
      norm_num at hk
    · simp [retained, headMass, Finset.sum_range_succ] at hk
      norm_num at hk
