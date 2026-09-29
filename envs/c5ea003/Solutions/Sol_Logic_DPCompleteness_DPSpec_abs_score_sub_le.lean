-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.abs_score_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:58:09.099957+00:00
-- url     : https://prove2.me/submissions/f5bed773-cf77-42da-a1a5-0641c013e1a0

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessStability
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, |D'.init s - D.init s| ≤ a)
    (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b) (f : ℕ → S) :
    ∀ n : ℕ, |D'.score f n - D.score f n| ≤ a + n • b := by
  intro n
  induction n with
  | zero => simpa using hinit (f 0)
  | succ n ih =>
    have hrw : D'.score f (n + 1) - D.score f (n + 1)
        = (D'.score f n - D.score f n)
          + (D'.step n (f n) (f (n + 1)) - D.step n (f n) (f (n + 1))) := by
      show (D'.score f n + D'.step n (f n) (f (n + 1)))
          - (D.score f n + D.step n (f n) (f (n + 1))) = _
      abel
    rw [hrw]
    refine (abs_add_le _ _).trans ?_
    rw [succ_nsmul, ← add_assoc]
    exact add_le_add ih (hstep n (f n) (f (n + 1)))
