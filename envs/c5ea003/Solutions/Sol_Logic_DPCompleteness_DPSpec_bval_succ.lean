-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.bval_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:19:08.873084+00:00
-- url     : https://prove2.me/submissions/b9e42d91-4641-435f-946b-c30b56bd7b41

/-
# `Logic.DPCompleteness.DPSpec.bval_succ`
Target `ceb92a60` (WA,WA,WA,WA,CE).

The definition IS the target's right-hand side:
    def bval (D : DPSpec S W) : ℕ → ℕ → S → W
      | _, 0, _ => 0
      | k, (m + 1), s => (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun t => D.step k s t + D.bval (k + 1) m t)
so this is the second equation lemma and holds by `rfl`.

THE WHOLE DIFFICULTY IS THE BINDER LIST, copied VERBATIM from this target's own WA — SIXTEEN
instances, with Fintype S / Nonempty S / LinearOrder W repeated FOUR times, because the bundle's
sections at lines 68, 96, 105 and 119 each re-declare them and Lean keeps every copy:
  [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]
  [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
  [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
  [Fintype S] [Nonempty S] [LinearOrder W]
Four people wrote a correct `rfl` and were rejected on exactly this.
-/
import Mathlib
import Definitions.Def_Logic_DPCompleteness

set_option maxHeartbeats 400000

open Logic.DPCompleteness Finset

open Logic.DPCompleteness in
/-- **The target, verbatim.** -/
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W]
    (D : DPSpec S W) (k m : ℕ) (s : S) :
    D.bval k (m + 1) s
      = (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun t => D.step k s t + D.bval (k + 1) m t) := by
  rfl
