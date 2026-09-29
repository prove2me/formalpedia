-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.score_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:13:28.319632+00:00
-- url     : https://prove2.me/submissions/0e9cb4c9-7ce0-49f1-9bb5-f4513e3db666

/-
# `Logic.DPCompleteness.DPSpec.score_succ`
Target `fd6bfc47`. BINDERS from this target's OWN WA: `[AddCommMonoid W]` ONLY — `score` is declared
at bundle line 56, BEFORE the `Value` section that opens `Fintype S`, `Nonempty S`, `LinearOrder W`.
Its sibling `val_succ` legitimately carries all four.

The definition reads `| (n + 1) => D.score f n + D.step n (f n) (f (n + 1))`, so the target IS the
second equation lemma and holds definitionally.

NOTE: written `:= by rfl`, not `:= rfl` — the live guard requires the literal `:= by` form.
-/
import Mathlib
import Definitions.Def_Logic_DPCompleteness

set_option maxHeartbeats 400000

open Logic.DPCompleteness Finset

open Logic.DPCompleteness in
/-- **The target, verbatim.** -/
theorem solution {S W : Type*} [AddCommMonoid W] (D : DPSpec S W) (f : ℕ → S) (n : ℕ) :
    D.score f (n + 1) = D.score f n + D.step n (f n) (f (n + 1)) := by
  rfl
