-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.val_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:30:39.940624+00:00
-- url     : https://prove2.me/submissions/f8d34e8b-08ec-493e-a699-928c2b04937d

import Mathlib
import Definitions.Def_Logic_DPCompleteness
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    (D : DPSpec S W) (n : ℕ) (t : S) :
    D.val (n + 1) t =
      (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => D.val n s + D.step n s t) := by
  rfl
