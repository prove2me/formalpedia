-- Prove2me | Theorems.Thm_ReflectiveTypeTheory_godelian_satisfiable_in_K
-- name    : ReflectiveTypeTheory.godelian_satisfiable_in_K
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:52:01.920118+00:00
-- url     : https://prove2.me/theorems/2781c8a9-54d0-44d1-97e4-1724041e5b1c
-- title:
--   The Gödelian reflective sentence is a satisfiable, well-typed term.
-- statement:
--   **The Gödelian reflective sentence is a satisfiable, well-typed term.**
--   There is a model and world at which `□A ∧ ¬□□A` holds.
--
--   ```lean
--   theorem ReflectiveTypeTheory.godelian_satisfiable_in_K:
--       sat Kmodel (godelianReflection (Form.atom 0)) KW.wa := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/ReflectiveTypeTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/ReflectiveTypeTheory.lean#L151

-- Thm stub generated from MachineLearning/ReflectiveTypeTheory.lean
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

theorem ReflectiveTypeTheory.godelian_satisfiable_in_K:
    sat Kmodel (godelianReflection (Form.atom 0)) KW.wa := by sorry
