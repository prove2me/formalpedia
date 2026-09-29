-- Prove2me | solution 2 for Logic.DPCompleteness.DPSpec.val_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:21:20.911535+00:00
-- url     : https://prove2.me/submissions/54ce5456-602a-4fa3-b4ed-1c35a46e2596

import Mathlib
import Definitions.Def_Logic_DPCompleteness
open Logic.DPCompleteness in
theorem solution {S : Type*} {W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S]
    [LinearOrder W] [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W]
    [IsOrderedCancelAddMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [IsOrderedCancelAddMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]
    [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W] {D D' : DPSpec S W}
    (hinit : ∀ s, D.init s ≤ D'.init s)
    (hstep : ∀ i s t, D.step i s t ≤ D'.step i s t) :
    ∀ (n : ℕ) (s : S), D.val n s ≤ D'.val n s := by
  intro n
  induction n with
  | zero => intro s; exact hinit s
  | succ n ih =>
    intro t
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun s => D.val n s + D.step n s t) ≤ D'.val (n + 1) t
    refine Finset.sup'_le _ _ (fun s _ => ?_)
    refine le_trans ?_
      (Finset.le_sup' (fun s => D'.val n s + D'.step n s t) (Finset.mem_univ s))
    gcongr
    · exact ih s
    · exact hstep n s t
