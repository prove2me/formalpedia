-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.val_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:26:49.553979+00:00
-- url     : https://prove2.me/submissions/1c8c739f-c120-4f9d-9434-cc651d080372

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessStability
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] (D : DPSpec S W) (a b : W) :
    ∀ (n : ℕ) (s : S), (D.shift a b).val n s = D.val n s + (a + n • b) := by
  intro n
  induction n with
  | zero =>
    intro s
    simp [DPSpec.val, DPSpec.shift]
  | succ n ih =>
    intro t
    simp only [DPSpec.val]
    -- adding a constant commutes with the finite supremum
    have key := Finset.comp_sup'_eq_sup'_comp (s := Finset.univ) Finset.univ_nonempty
      (f := fun s => D.val n s + D.step n s t) (fun x : W => x + (a + (n + 1) • b)) (by
        intro x y
        rcases le_total x y with h | h
        · rw [sup_of_le_right h, sup_of_le_right (add_le_add h le_rfl)]
        · rw [sup_of_le_left h, sup_of_le_left (add_le_add h le_rfl)])
    simp only [Function.comp_def] at key
    rw [key]
    refine Finset.sup'_congr _ rfl (fun s _ => ?_)
    rw [ih s]
    simp only [DPSpec.shift, succ_nsmul]
    abel
