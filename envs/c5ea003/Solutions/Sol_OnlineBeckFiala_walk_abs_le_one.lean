-- Prove2me | solution 1 for OnlineBeckFiala.walk_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:31:03.144818+00:00
-- url     : https://prove2.me/submissions/094507f3-f16b-4a85-a670-13c94509b95e

import Mathlib
import Definitions.Def_Novelty_OnlineBeckFialaWalk

open OnlineBeckFiala

theorem solution (a : ℕ → ℝ) (ha : ∀ s, |a s| ≤ 1) :
    ∀ t, |walk a t| ≤ 1 := by
  intro t
  induction t with
  | zero => simp [walk]
  | succ t ih =>
      set s := walk a t
      have hsabs : |s| ≤ 1 := ih
      have hslo : -1 ≤ s := (abs_le.mp hsabs).1
      have hshi : s ≤ 1 := (abs_le.mp hsabs).2
      by_cases hs : s ≤ 0
      · -- walk (t+1) = s + |a t|
        have : walk a (t + 1) = s + |a t| := by simp [walk, s, hs]
        rw [this]
        refine abs_le.mpr ⟨?_, ?_⟩
        · nlinarith [abs_nonneg (a t)]
        · nlinarith [ha t]
      · push_neg at hs
        have : walk a (t + 1) = s - |a t| := by
          simp [walk, s, not_le.mpr hs]
          ring
        rw [this]
        refine abs_le.mpr ⟨?_, ?_⟩
        · nlinarith [ha t]
        · nlinarith [abs_nonneg (a t)]
