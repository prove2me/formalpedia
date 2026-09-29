-- Prove2me | solution 1 for AlmostLossless.foldl_scanStep_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:42:41.229446+00:00
-- url     : https://prove2.me/submissions/d888e636-b50d-4e72-8e1b-c625d270697a

/-
# `AlmostLossless.foldl_scanStep_eq_filter`
Target `c83e7650` (WA x5). Binders from its own WA: `{S}` plus explicit `(p) (L) (st)` — no instances,
despite the Hashing bundle declaring `[DecidableEq S] [DecidableEq M]`.

`scanStep p st t = if p t then scanStepAll st t else st`, so induction on `L` GENERALISING THE
ACCUMULATOR `st`: when `p a` holds, `scanStep` is literally `scanStepAll` and `List.filter_cons`
keeps `a` at the head of the filtered list, so both sides take the same step; otherwise both drop it.
-/
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme

set_option maxHeartbeats 400000

open AlmostLossless Finset

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {S : Type*} (p : S → Bool) (L : List S) (st : ScanState S) :
    L.foldl (scanStep p) st = (L.filter p).foldl scanStepAll st := by
  induction L generalizing st with
  | nil => simp
  | cons a L ih =>
      cases h : p a <;> simp [List.filter_cons, h, scanStep, scanStepAll, ih]
