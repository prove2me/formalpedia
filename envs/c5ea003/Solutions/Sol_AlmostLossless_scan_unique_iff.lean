-- Prove2me | solution 1 for AlmostLossless.scan_unique_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:48:44.504372+00:00
-- url     : https://prove2.me/submissions/813926b2-bb02-4b4f-a90a-65d04bcd2b1c

/-
# `AlmostLossless.scan_unique_iff`
Target `8c9f3e55` (WA x5). Binders from its own WA: `{S}` plus explicit `(p) (L) (t)`.

`scan p L = L.foldl (scanStep p) .empty`, so this reduces to the behaviour of `scanStepAll` on the
FILTERED list: `.empty` for `[]`, `.unique a` for `[a]`, and `.ambiguous` from two elements on
(absorbing). Only `[t]` yields `.unique t`.

NOTE: the fold lemma must generalise the ACCUMULATOR (`st`), not the witness `t` — the recursive
step changes the accumulator, so a `t`-generalised hypothesis cannot reach `foldl … (unique a) L`.
-/
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme

set_option maxHeartbeats 400000

open AlmostLossless Finset

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {S : Type*} (p : S → Bool) (L : List S) (t : S) :
    scan p L = .unique t ↔ L.filter p = [t] := by
  have hstep : ∀ (K : List S) (st : ScanState S),
      K.foldl (scanStep p) st = (K.filter p).foldl scanStepAll st := by
    intro K
    induction K with
    | nil => intro st; simp
    | cons a K ih =>
        intro st
        cases h : p a <;> simp [List.filter_cons, h, scanStep, scanStepAll, ih]
  have amb : ∀ (M : List S), M.foldl scanStepAll ScanState.ambiguous = .ambiguous := by
    intro M
    induction M with
    | nil => rfl
    | cons a M ih => simpa [scanStepAll] using ih
  have hfold : ∀ (M : List S), M.foldl scanStepAll ScanState.empty = .unique t ↔ M = [t] := by
    intro M
    match M with
    | [] => simp
    | [a] => simp [scanStepAll]
    | a :: b :: M' => simp [scanStepAll, amb]
  rw [scan, hstep L ScanState.empty]
  exact hfold (L.filter p)
