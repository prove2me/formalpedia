-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.transcript_opened_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:45:29.306675+00:00
-- url     : https://prove2.me/submissions/c2ef3cd6-9949-4ae6-9d2b-4e139a20499c

/-
# `MachineLearning.CommittedLocalOracleZK.transcript_opened_card_le`
Target `a95fe4b1` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen **CLEAN**. Gift: **SAFE**.

BINDERS — expected type from a WA, VERBATIM:
    ∀ {I A C O Rc Rv P} [DecidableEq I] [Fintype I]
      (Pr : CommittedOracle I A C O Rc Rv P) (p : P) (r : Rv),
      {i | (restrictTo (Pr.Q r) (Pr.proof p) i).isSome = true}.card ≤ Pr.qbound
TWO instances only — `[DecidableEq I] [Fintype I]` — even though the enclosing section (line 140)
also opens `Fintype Rc/Rv/P/S` and (line 141) `DecidableEq A/C/O/Rv`. Lean includes only what the
declaration USES, and this one mentions no commitment, no opening data and no randomness beyond `r`.
Five submitters have been rejected on type here five times each; that staged-`variable` layout is why.

NOTE ON `{i | … }.card`. This is NOT `Set.ncard`: it is Mathlib's notation for `Finset.filter … univ`,
which is why the platform's own statement text renders the same thing as `univ.filter …`. Reading it
as a Set would send the proof down a completely wrong road.

MATHS — one unfolding and one structure field.
    restrictTo T f = fun i => if i ∈ T then some (f i) else none
so `(restrictTo T f i).isSome` is true exactly when `i ∈ T`. The filtered set is therefore `Pr.Q r`
itself, and the bound is the structure's OWN field
    query_card_le : ∀ r, (Q r).card ≤ qbound
i.e. the constant-query-complexity axiom the protocol carries. Nothing is estimated; the theorem is
the definition of `restrictTo` composed with a field lookup.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 400000

open MachineLearning.CommittedLocalOracleZK Finset

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A C O Rc Rv P : Type*} [DecidableEq I] [Fintype I]
    (Pr : CommittedOracle I A C O Rc Rv P) (p : P) (r : Rv) :
    (Finset.univ.filter fun i => (restrictTo (Pr.Q r) (Pr.proof p) i).isSome).card ≤ Pr.qbound := by
  have hset : (Finset.univ.filter fun i => (restrictTo (Pr.Q r) (Pr.proof p) i).isSome)
      = Pr.Q r := by
    ext i
    simp [restrictTo]
  rw [hset]
  exact Pr.query_card_le r
