-- Prove2me | solution 1 for AlmostLossless.scanCost_snd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:25:05.109104+00:00
-- url     : https://prove2.me/submissions/b71772d9-8e09-44ad-b0e8-1590d8151f0b

/-
# `AlmostLossless.scanCost_snd`
Target `a31150d2` (WA x6 — the highest count I have seen). Gift: SAFE.

BINDERS VERBATIM from its own WA: `{α} {M} (h) (i) (l)` — NO instances. That matches
`section Decoder`'s `variable {α : Type*} {M : ℕ}` at bundle line 85, and NOT the surrounding
`Universal`/`Scheme` sections, which add `[Fintype α] [DecidableEq α]`. Six people wrote compiling
proofs and lost on exactly this.

MATHS. The second component of `scanCost` ignores the `if` entirely:
    | [] => ([], 0)
    | y :: ys => (if h y = i then y :: p.1 else p.1, p.2 + 1)
so it increments once per element regardless of the hash test. A one-step list induction.

NOTE the SIBLING `90468277 scanCost_fst` is GIFT-EXPOSED (gifts cc3ec7ac) and is NOT being shipped —
same file, same definition, opposite verdict, because the first component is what other sketches use.
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding

set_option maxHeartbeats 400000

open AlmostLossless Finset

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} {M : ℕ} (h : α → Fin M) (i : Fin M) (l : List α) :
    (scanCost h i l).2 = l.length := by
  induction l with
  | nil => rfl
  | cons y ys ih => simpa [scanCost] using ih
