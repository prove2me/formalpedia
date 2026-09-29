-- Prove2me | Definitions.Def_MachineLearning_ReflectiveTypeTheory
-- name    : MachineLearning_ReflectiveTypeTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:30.570167+00:00
-- url     : https://prove2.me/theorems/82d80866-53d3-4af7-91bd-ca9b88636dc3
-- title:
--   Aether Catalog definitions — MachineLearning_ReflectiveTypeTheory
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.ReflectiveTypeTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/ReflectiveTypeTheory.lean by skeleton subtraction
import Mathlib
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


namespace ReflectiveTypeTheory

/-! ## Syntax -/

/-- Propositional modal formulas.  `box p` is read "`p` is provable". -/
inductive Form where
  | atom : ℕ → Form
  | bot : Form
  | imp : Form → Form → Form
  | box : Form → Form
deriving DecidableEq

/-- Negation `¬p := p → ⊥`. -/
def Form.neg (p : Form) : Form := Form.imp p Form.bot

/-- Conjunction, defined classically via `¬(p → ¬q)`. -/
def Form.and (p q : Form) : Form := Form.neg (Form.imp p (Form.neg q))

/-- The dual modality `◇p := ¬□¬p`. -/
def Form.dia (p : Form) : Form := (Form.box p.neg).neg

/-- The reflective Gödelian sentence "`A` is provable but not provably provable":
`□A ∧ ¬□□A`. -/
def godelianReflection (A : Form) : Form := (A.box).and (A.box.box).neg

/-! ## Kripke semantics -/

/-- A Kripke model: a set of worlds `W`, an accessibility relation `R`, and a
valuation `V` of atoms.  `R w v` means "`v` is accessible from `w`". -/
structure Model where
  W : Type
  R : W → W → Prop
  V : ℕ → W → Prop

/-- Satisfaction of a formula at a world. `box p` holds at `w` iff `p` holds at
every accessible world. -/
def sat (M : Model) : Form → M.W → Prop
  | Form.atom n, w => M.V n w
  | Form.bot, _ => False
  | Form.imp p q, w => sat M p w → sat M q w
  | Form.box p, w => ∀ v, M.R w v → sat M p v

/-- A formula is *valid* in a model if it holds at every world. -/
def valid (M : Model) (p : Form) : Prop := ∀ w, sat M p w




/-! ## The normal modal logic `K` -/




/-! ## "Provable but not provably provable" is satisfiable

We build an explicit three-world, non-transitive model `Kmodel` and a world at
which `□A ∧ ¬□□A` holds.  The worlds form a chain `wa → wb → wc`; the atom `A`
is true exactly at `wb`.  Then at `wa`: every accessible world (`wb`) satisfies
`A`, so `□A` holds; but `wb` accesses `wc` where `A` fails, so `□A` fails at
`wb`, whence `□□A` fails at `wa`. -/

/-- The three worlds of the witnessing model. -/
inductive KW | wa | wb | wc
deriving DecidableEq

/-- A non-transitive Kripke model witnessing `□A ∧ ¬□□A`. -/
def Kmodel : Model where
  W := KW
  R := fun a b => (a = KW.wa ∧ b = KW.wb) ∨ (a = KW.wb ∧ b = KW.wc)
  V := fun _ w => w = KW.wb



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

/-- A concrete `GL` model on the naturals: `R a b` iff `b < a`. -/
def GLmodel : Model where
  W := ℕ
  R := fun a b => b < a
  V := fun _ _ => True





end ReflectiveTypeTheory


