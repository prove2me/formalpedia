-- Prove2me | solution 1 for ReflectiveTypeTheory.loeb_valid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:34.250926+00:00
-- url     : https://prove2.me/submissions/95657266-d62b-4b3e-a0be-cd5b8570c570

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
theorem solution(M : Model) (htrans : Transitive M.R)
    (hwf : WellFounded (fun a b => M.R b a)) (A : Form) (w : M.W) :
    sat M (Form.imp (Form.box (Form.imp (Form.box A) A)) (Form.box A)) w := by
  intro hbox
  show ∀ v, M.R w v → sat M A v
  by_contra hcon
  push_neg at hcon
  obtain ⟨v0, hv0, hnv0⟩ := hcon
  -- Take an `R`-maximal accessible world `u` at which `A` fails.
  obtain ⟨u, huS, hmax⟩ :=
    hwf.has_min {x | M.R w x ∧ ¬ sat M A x} ⟨v0, hv0, hnv0⟩
  obtain ⟨hRwu, hnAu⟩ := huS
  -- From `□(□A → A)` at `w` and `R w u` we get `□A → A` at `u`.
  have himp := hbox u hRwu
  have hnbox : ¬ sat M (Form.box A) u := fun hb => hnAu (himp hb)
  -- Hence some `u'` accessible from `u` fails `A`; by transitivity `R w u'`.
  have hex : ∃ u', M.R u u' ∧ ¬ sat M A u' := by
    by_contra hc; push_neg at hc; exact hnbox hc
  obtain ⟨u', hRuu', hnAu'⟩ := hex
  -- This contradicts the maximality of `u`.
  exact hmax u' ⟨htrans hRwu hRuu', hnAu'⟩ hRuu'
