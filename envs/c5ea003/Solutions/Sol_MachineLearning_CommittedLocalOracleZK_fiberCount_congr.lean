-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.fiberCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:49:06.753884+00:00
-- url     : https://prove2.me/submissions/b005dd4c-041f-480d-ae0b-eed76d2c10b1

/-
# `MachineLearning.CommittedLocalOracleZK.fiberCount_congr`
Target `8fbe45bf` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen **CLEAN**. Gift: **SAFE**.

BINDERS — this bundle is a WA MINE: seven of eight Open targets carry `WA,WA,WA,WA,WA`, i.e. five
compiled proofs rejected on TYPE each. The cause is that the required instances differ PER THEOREM,
because the file opens instances in stages:
    line  91  variable {I A C O Rc Rv P S : Type*}
    line 117  variable [DecidableEq I]
    line 140  variable [Fintype I] [Fintype Rc] [Fintype Rv] [Fintype P] [Fintype S]
    line 141  variable [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
Lean includes only the ones a declaration USES. Expected type, from a WA, VERBATIM:
    ∀ {I A C O Rc Rv P} [DecidableEq I] [Fintype Rc] [DecidableEq C] [DecidableEq O]
      {Pr : CommittedOracle I A C O Rc Rv P}, PerfectlyHidesUnopened Pr →
      ∀ (T : Finset I) (u v : I → A), (∀ i ∈ T, u i = v i) → ∀ (c : C) (o : O), …
FOUR instances only — no `Fintype I`, no `DecidableEq A`, no `S` at all, and `Pr` IMPLICIT.
That matches `fiberCount`'s own telescope: `univ : Finset Rc` needs `Fintype Rc`, the predicate
`Pr.com u ρ = c ∧ Pr.openInfo u ρ T = o` needs `DecidableEq C` and `DecidableEq O`, and the
structure needs `DecidableEq I`.

MATHS.
    fiberCount Pr u T c o = (univ.filter fun ρ => Pr.com u ρ = c ∧ Pr.openInfo u ρ T = o).card
    PerfectlyHidesUnopened Pr = ∀ T u v, (∀ i ∈ T, u i = v i) →
        ∃ e : Rc ≃ Rc, ∀ ρ, Pr.com u ρ = Pr.com v (e ρ) ∧ Pr.openInfo u ρ T = Pr.openInfo v (e ρ) T
So hiding hands over the bijection OUTRIGHT. Under `e`, `ρ` satisfies the `u`-predicate exactly when
`e ρ` satisfies the `v`-predicate, and the two fibres have equal cardinality.

PROBED, NOT GUESSED — read from Mathlib source, not recalled:
  * `Finset.card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t`  — Data/Finset/Card.lean:410
    This is the right tool precisely BECAUSE hiding supplies an `Equiv`; `card_bij` (line 348) would
    demand four separate obligations and `card_nbij'` (403) two `Set.MapsTo`s, all redundant here.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 400000

open MachineLearning.CommittedLocalOracleZK Finset

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A C O Rc Rv P : Type*} [DecidableEq I] [Fintype Rc] [DecidableEq C]
    [DecidableEq O] {Pr : CommittedOracle I A C O Rc Rv P}
    (hH : PerfectlyHidesUnopened Pr) (T : Finset I) (u v : I → A)
    (huv : ∀ i ∈ T, u i = v i) (c : C) (o : O) :
    fiberCount Pr u T c o = fiberCount Pr v T c o := by
  obtain ⟨e, he⟩ := hH T u v huv
  show (Finset.univ.filter fun ρ => Pr.com u ρ = c ∧ Pr.openInfo u ρ T = o).card
      = (Finset.univ.filter fun ρ => Pr.com v ρ = c ∧ Pr.openInfo v ρ T = o).card
  refine Finset.card_equiv e ?_
  intro ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [(he ρ).1, (he ρ).2]
