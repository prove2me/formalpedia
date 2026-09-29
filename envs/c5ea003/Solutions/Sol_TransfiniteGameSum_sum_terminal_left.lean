-- Prove2me | solution 1 for TransfiniteGameSum.sum_terminal_left
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:13.638221+00:00
-- url     : https://prove2.me/submissions/38eb9619-d664-460b-bd02-d1f50c1dfc3f

import Mathlib
import Definitions.Def_MachineLearning_TransfiniteGameSum

open TransfiniteGameSum

variable {P : Type*} (mv : P → P → Prop) (hwf : WellFounded (fun q p : P => mv p q))

theorem solution (a : P) (ha : Terminal mv a) (b : P) :
    Wsum mv hwf (a, b) ↔ W mv hwf b := by
  refine hwf.induction (C := fun b => Wsum mv hwf (a, b) ↔ W mv hwf b) b ?_
  intro b IH
  constructor
  · intro hsum
    obtain ⟨q, hmv, hlose⟩ := (W_fix (sumMv mv) (sumWf mv hwf) (a, b)).1 hsum
    rcases hmv with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩
    · exact (ha ⟨q.1, hm1⟩).elim
    · subst hm1
      have hineq := IH q.2 hm2
      exact (W_fix mv hwf b).2 ⟨q.2, hm2, fun hw => hlose (hineq.2 hw)⟩
  · intro hw
    obtain ⟨q, hmv, hlose⟩ := (W_fix mv hwf b).1 hw
    refine (W_fix (sumMv mv) (sumWf mv hwf) (a, b)).2 ⟨(a, q), Or.inr ⟨rfl, hmv⟩, ?_⟩
    exact fun hs => hlose ((IH q hmv).1 hs)
