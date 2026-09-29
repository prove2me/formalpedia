-- Prove2me | solution 1 for TransfiniteGameSum.diag_loss
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:18:59.919671+00:00
-- url     : https://prove2.me/submissions/76c14223-dc3d-49f8-8c65-c6f7e4e0f841

import Mathlib
import Definitions.Def_MachineLearning_TransfiniteGameSum

open TransfiniteGameSum

variable {P : Type*} (mv : P → P → Prop) (hwf : WellFounded (fun q p : P => mv p q))

theorem solution (a : P) : ¬ Wsum mv hwf (a, a) := by
  refine hwf.induction (C := fun a => ¬ Wsum mv hwf (a, a)) a ?_
  intro a IH hwin
  obtain ⟨q, hmv, hlose⟩ := (W_fix (sumMv mv) (sumWf mv hwf) (a, a)).1 hwin
  rcases hmv with hleft | hright
  · -- Move in the left component: q = (b, a) with mv a b
    obtain ⟨b, rfl⟩ : ∃ b, q = (b, a) := ⟨q.1, by
      cases q with
      | mk b c =>
        obtain ⟨hmv_ab, rfl⟩ := hleft
        rfl⟩
    obtain ⟨hmv_ab, _⟩ := hleft
    -- From (b, a) move right to (b, b)
    have hW : Wsum mv hwf (b, a) := by
      refine (W_fix (sumMv mv) (sumWf mv hwf) (b, a)).2 ?_
      refine ⟨(b, b), Or.inr ⟨rfl, hmv_ab⟩, IH b hmv_ab⟩
    exact hlose hW
  · -- Move in the right component: q = (a, b) with mv a b
    obtain ⟨b, rfl⟩ : ∃ b, q = (a, b) := ⟨q.2, by
      cases q with
      | mk c b =>
        obtain ⟨rfl, hmv_ab⟩ := hright
        rfl⟩
    obtain ⟨_, hmv_ab⟩ := hright
    have hW : Wsum mv hwf (a, b) := by
      refine (W_fix (sumMv mv) (sumWf mv hwf) (a, b)).2 ?_
      refine ⟨(b, b), Or.inl ⟨hmv_ab, rfl⟩, IH b hmv_ab⟩
    exact hlose hW
