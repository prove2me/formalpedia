-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.score_le_val
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:17:25.004969+00:00
-- url     : https://prove2.me/submissions/333c2e83-c1a1-4e52-9449-a169b1037b9c

import Mathlib
import Definitions.Def_Logic_DPCompleteness
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] (D : DPSpec S W) (f : ℕ → S) : ∀ n : ℕ, D.score f n ≤ D.val n (f n) := by
  intro m
  induction m with
  | zero => exact le_of_eq rfl
  | succ m ih =>
    show D.score f m + D.step m (f m) (f (m + 1)) ≤ D.val (m + 1) (f (m + 1))
    have h1 : D.score f m + D.step m (f m) (f (m + 1))
        ≤ D.val m (f m) + D.step m (f m) (f (m + 1)) := by gcongr
    refine h1.trans ?_
    exact Finset.le_sup' (fun s => D.val m s + D.step m s (f (m + 1))) (Finset.mem_univ (f m))
