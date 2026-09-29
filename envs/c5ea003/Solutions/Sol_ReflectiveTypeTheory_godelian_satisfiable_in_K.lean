-- Prove2me | solution 1 for ReflectiveTypeTheory.godelian_satisfiable_in_K
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:33.573594+00:00
-- url     : https://prove2.me/submissions/d199b0ab-9cbd-4839-b8bd-ae3651608271

-- Sol generated from MachineLearning/ReflectiveTypeTheory.lean
import Mathlib
import Definitions.Def_MachineLearning_ReflectiveTypeTheory
/-
# Reflective Type Theory: Proving Things About Proving Things

This file formalizes a small *reflective* propositional logic in which a
proposition may refer to its own provability, and studies the well-typed term

  "this proposition is provable but not provably provable"    (□A ∧ ¬□□A).

The modality `□` is read as *provability*, following the standard reading of
provability logic where `□A` means "`A` is provable".  We give a Kripke
semantics for the language and establish:

* `godelian_satisfiable_in_K` — the sentence `□A ∧ ¬□□A` is a *satisfiable*,
  well-typed term: there is a (non-transitive) model and world where it holds.
  Thus a reflective system whose provability predicate is *not* provably
  transitive can genuinely express "provable but not provably provable".

* `axiom4_of_transitive` — in any transitive frame the axiom `4` (`□A → □□A`)
  is valid.  This is exactly the semantic content of *Σ₁-completeness*
  ("if `A` is provable then it is provably provable").

* `godelian_unsat_in_transitive` — consequently, in every transitive frame
  (in particular in the frames of Gödel–Löb provability logic `GL`) the
  sentence `□A ∧ ¬□□A` is *unsatisfiable*.  So the "provable but not provably
  provable" phenomenon is impossible precisely when provability is provably
  transitive.

* `Kmodel_not_transitive` — the witnessing model above is not transitive,
  confirming that the contrast between the two results is real.

We further develop the semantics enough to prove the two landmark theorems of
provability logic:

* `axiomK`, `necessitation`, `axiomT_of_reflexive`, `sat_dia` — the normal
  modal logic `K` and the dual `◇`.

* `loeb_valid` — **Löb's theorem**: on transitive, converse-well-founded
  frames (the `GL` frames) the Löb schema `□(□A → A) → □A` is valid.

* `goedel_second_incompleteness` — **Gödel's second incompleteness theorem**
  as a corollary: on `GL` frames `□(¬□⊥) → □⊥`, i.e. a consistent system that
  is a `GL` frame cannot prove its own consistency.

Everything is elementary and self-contained (only `Mathlib`'s `WellFounded`
infrastructure is used, for Löb's theorem).
-/


open ReflectiveTypeTheory

/-! ## Syntax -/






/-! ## Kripke semantics -/





/-- Satisfaction of the defined conjunction agrees with meta-level `∧`. -/
lemma sat_and (M : Model) (p q : Form) (w : M.W) :
    sat M (p.and q) w ↔ (sat M p w ∧ sat M q w) := by
  simp [Form.and, Form.neg, sat]


/-! ## The normal modal logic `K` -/




/-! ## "Provable but not provably provable" is satisfiable

We build an explicit three-world, non-transitive model `Kmodel` and a world at
which `□A ∧ ¬□□A` holds.  The worlds form a chain `wa → wb → wc`; the atom `A`
is true exactly at `wb`.  Then at `wa`: every accessible world (`wb`) satisfies
`A`, so `□A` holds; but `wb` accesses `wc` where `A` fails, so `□A` fails at
`wb`, whence `□□A` fails at `wa`. -/





/-! ## Transitive frames: provability is provably transitive

On transitive frames the axiom `4` holds, which is the semantic form of
Σ₁-completeness: whatever is provable is provably provable.  Hence the
reflective sentence `□A ∧ ¬□□A` becomes *unsatisfiable*. -/



/-! ## Löb's theorem and Gödel's second incompleteness theorem

The frames of Gödel–Löb provability logic `GL` are the transitive,
converse-well-founded frames.  On these frames the Löb schema is valid, and
Gödel's second incompleteness theorem follows by taking `A := ⊥`. -/



/-! ## A concrete `GL` frame

To confirm the `GL` theorems above are non-vacuous, here is an explicit
transitive, converse-well-founded model on `ℕ` with `R a b := b < a`. -/







open ReflectiveTypeTheory in
theorem solution:
    sat Kmodel (godelianReflection (Form.atom 0)) KW.wa := by
  rw [godelianReflection, sat_and]
  constructor
  · -- `□A` at `wa`: the only accessible world is `wb`, where `A` is true.
    intro v hv
    rcases hv with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (by decide)
  · -- `¬□□A` at `wa`: `wb` is accessible and accesses `wc`, where `A` fails.
    intro h
    have := h KW.wb (Or.inl ⟨rfl, rfl⟩) KW.wc (Or.inr ⟨rfl, rfl⟩)
    exact absurd (show KW.wc = KW.wb from this) (by decide)
