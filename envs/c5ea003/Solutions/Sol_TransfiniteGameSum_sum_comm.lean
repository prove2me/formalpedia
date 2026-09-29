-- Prove2me | solution 1 for TransfiniteGameSum.sum_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:58:50.623921+00:00
-- url     : https://prove2.me/submissions/e3fe9e3b-a6e6-41de-a3d7-4afbfd35f282

import Mathlib
import Definitions.Def_MachineLearning_TransfiniteGameSum
open TransfiniteGameSum in
theorem solution {P : Type*} (mv : P → P → Prop)
    (hwf : WellFounded (fun q p : P => mv p q)) (a b : P) :
    Wsum mv hwf (a, b) ↔ Wsum mv hwf (b, a) := by
  have hswap : ∀ r q : P × P, sumMv mv r q → sumMv mv (r.2, r.1) (q.2, q.1) := by
    intro r q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  have key : ∀ r : P × P, (Wsum mv hwf r ↔ Wsum mv hwf (r.2, r.1)) := by
    intro r
    induction r using (sumWf mv hwf).induction with
    | _ r ih =>
      constructor
      · intro hr
        obtain ⟨q, hmv, hnq⟩ := W_has_move (sumMv mv) (sumWf mv hwf) r hr
        refine (W_fix (sumMv mv) (sumWf mv hwf) (r.2, r.1)).2 ⟨(q.2, q.1), hswap r q hmv, ?_⟩
        intro hcon
        exact hnq ((ih q hmv).mpr hcon)
      · intro hr
        obtain ⟨q, hmv, hnq⟩ := W_has_move (sumMv mv) (sumWf mv hwf) (r.2, r.1) hr
        have hmv' : sumMv mv r (q.2, q.1) := hswap (r.2, r.1) q hmv
        refine (W_fix (sumMv mv) (sumWf mv hwf) r).2 ⟨(q.2, q.1), hmv', ?_⟩
        intro hcon
        exact hnq ((ih (q.2, q.1) hmv').mp hcon)
  exact key (a, b)
