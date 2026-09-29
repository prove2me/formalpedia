-- Prove2me | solution 1 for Bridges.AttentionKneeGeometry.geometric_coarse_grid_overestimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:46:41.64527+00:00
-- url     : https://prove2.me/submissions/92fc54e0-e7c3-4450-8bfc-c46afc02f038

import Mathlib
import Definitions.Def_Bridges_AttentionKneeGeometry
open Finset Bridges.AttentionKneeGeometry in
theorem solution :
    gridKnee {2, 4, 8, 16} geometricProfile 0.98 = 8 ∧
      gridKnee {2, 4, 6, 8, 16} geometricProfile 0.98 = 6 ∧
      knee geometricProfile 0.98 = 6 := by
  -- `mass k = 1 - 2^(-k)`
  have hm : ∀ k, mass geometricProfile k = 1 - (1 / 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp [mass]
    | succ k ih =>
      rw [mass, Finset.sum_range_succ, ← mass, ih]
      simp only [geometricProfile]
      ring
  -- the gate `0.98` is passed exactly from `k = 6` on (`2^6 = 64 ≥ 50 > 32`)
  have hpass : ∀ k : ℕ, (0.98 : ℝ) ≤ mass geometricProfile k ↔ 6 ≤ k := by
    intro k
    rw [hm]
    constructor
    · intro h
      by_contra hk
      have : (1 / 2 : ℝ) ^ 5 ≤ (1 / 2) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      norm_num at this h
      linarith
    · intro hk
      have : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      norm_num at this ⊢
      linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold gridKnee
    simp_rw [hpass]
    apply le_antisymm
    · exact Nat.sInf_le ⟨by simp, by norm_num⟩
    · refine le_csInf ⟨8, by simp, by norm_num⟩ (fun k hk => ?_)
      obtain ⟨hk, h6⟩ := hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      omega
  · unfold gridKnee
    simp_rw [hpass]
    apply le_antisymm
    · exact Nat.sInf_le ⟨by simp, le_refl 6⟩
    · exact le_csInf ⟨6, by simp, le_refl 6⟩ (fun k hk => hk.2)
  · unfold knee
    simp_rw [hpass]
    exact le_antisymm (Nat.sInf_le (le_refl 6)) (le_csInf ⟨6, le_refl 6⟩ (fun k hk => hk))
