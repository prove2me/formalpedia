-- Prove2me | solution 1 for TropExpr.normalize_isNormalized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:13:51.148211+00:00
-- url     : https://prove2.me/submissions/a818da2d-695d-43be-b996-14bba96117bb

import Mathlib
import Definitions.Def_Bridges_TropicalNormalization
open TropExpr in
theorem solution (e : TropExpr) : isNormalized (TropExpr.normalize e) = true := by
  -- one-step unfoldings of the normal-form test away from the constant–constant patterns
  have hadd : ∀ a' b' : TropExpr, (∀ x y, ¬ (a' = .const x ∧ b' = .const y)) →
      isNormalized (.add a' b') = (isNormalized a' && isNormalized b') := by
    intro a' b' h
    cases a' <;> cases b' <;> simp_all [isNormalized]
  have htmin : ∀ a' b' : TropExpr, a' ≠ b' → (∀ x y, ¬ (a' = .const x ∧ b' = .const y)) →
      isNormalized (.tmin a' b') = (isNormalized a' && isNormalized b') := by
    intro a' b' hne h
    cases a' <;> cases b' <;> simp_all [isNormalized] <;> tauto
  induction e with
  | const r => rfl
  | var n => rfl
  | tmin a b iha ihb =>
    simp only [TropExpr.normalize]
    generalize TropExpr.normalize a = a' at iha ⊢
    generalize TropExpr.normalize b = b' at ihb ⊢
    by_cases hab : a' = b'
    · rw [if_pos hab]
      exact iha
    · rw [if_neg hab]
      cases a' <;> cases b' <;> first
        | rfl
        | (dsimp only
           rw [htmin _ _ hab (by simp)]
           simp only [Bool.and_eq_true]
           exact ⟨iha, ihb⟩)
  | add a b iha ihb =>
    simp only [TropExpr.normalize]
    generalize TropExpr.normalize a = a' at iha ⊢
    generalize TropExpr.normalize b = b' at ihb ⊢
    cases a' <;> cases b' <;> first
      | rfl
      | (dsimp only
         rw [hadd _ _ (by simp)]
         simp only [Bool.and_eq_true]
         exact ⟨iha, ihb⟩)
