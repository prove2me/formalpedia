-- Prove2me | solution 1 for TransfiniteGameSum.sum_terminal_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:17:23.867195+00:00
-- url     : https://prove2.me/submissions/79593056-5671-4d1e-a809-f2f1577e4ccb

import Mathlib
import Definitions.Def_MachineLearning_TransfiniteGameSum
open TransfiniteGameSum in
theorem solution {P : Type*} (mv : P → P → Prop) (hwf : WellFounded (fun q p : P => mv p q))
    (b : P) (hb : Terminal mv b) (a : P) :
    Wsum mv hwf (a, b) ↔ W mv hwf a := by
  induction a using hwf.induction with
  | _ a ih =>
    show W (sumMv mv) (sumWf mv hwf) (a, b) ↔ W mv hwf a
    rw [W_fix, W_fix]
    constructor
    · rintro ⟨⟨a', b'⟩, hmove, hnot⟩
      rcases hmove with ⟨hm, hbb⟩ | ⟨haa, hm⟩
      · refine ⟨a', hm, fun hW => hnot ?_⟩
        simp only at hbb
        subst hbb
        exact (ih a' hm).mpr hW
      · exact absurd ⟨b', hm⟩ hb
    · rintro ⟨a', hm, hnot⟩
      refine ⟨(a', b), Or.inl ⟨hm, rfl⟩, fun hWsum => hnot ?_⟩
      exact (ih a' hm).mp hWsum
