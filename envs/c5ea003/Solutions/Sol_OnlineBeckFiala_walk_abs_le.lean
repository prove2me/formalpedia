-- Prove2me | solution 1 for OnlineBeckFiala.walk_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:08.425025+00:00
-- url     : https://prove2.me/submissions/bec94696-bf30-44b3-bf6a-bb386aac9162

import Mathlib
import Definitions.Def_Novelty_OnlineBeckFialaWalk

open OnlineBeckFiala

theorem solution (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (ha : ∀ s, |a s| ≤ c) :
    ∀ t, |walk a t| ≤ c := by
  intro t
  induction t with
  | zero => simpa [walk] using hc
  | succ t ih =>
      simp only [walk]
      set s := walk a t with hsdef
      by_cases hs : s ≤ 0
      · have hsum : s + (if s ≤ 0 then |a t| else -|a t|) = s + |a t| := by simp [hs]
        rw [hsum]
        have hlo : -c ≤ s + |a t| := by
          have : -c ≤ s := (abs_le.mp ih).1
          nlinarith [abs_nonneg (a t)]
        have hhi : s + |a t| ≤ c := by nlinarith [hs, ha t, abs_nonneg (a t)]
        exact abs_le.mpr ⟨hlo, hhi⟩
      · push_neg at hs
        have hsum : s + (if s ≤ 0 then |a t| else -|a t|) = s - |a t| := by
          simp [not_le.mpr hs]; ring
        rw [hsum]
        have hhi : s - |a t| ≤ c := by nlinarith [abs_nonneg (a t), (abs_le.mp ih).2]
        have hlo : -c ≤ s - |a t| := by nlinarith [hs, ha t]
        exact abs_le.mpr ⟨hlo, hhi⟩
