-- Prove2me | Definitions.Def_Novelty_MultiverseSetTheory
-- name    : Novelty_MultiverseSetTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:55.67398+00:00
-- url     : https://prove2.me/theorems/15b7fd0d-0a73-4951-9153-9ee198b994c7
-- title:
--   Aether Catalog definitions — Novelty_MultiverseSetTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MultiverseSetTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MultiverseSetTheory.lean by skeleton subtraction
import Mathlib
/-
# Multiverse Set Theory — Mathematics Across Branches

A self-contained formalization of the *combinatorial core* of Hamkins'
set-theoretic multiverse.

We abstract a "model of ZFC" to a **world**: a truth assignment `α → Bool` on a
type `α` of atomic set-theoretic assertions (e.g. `CH`, `V = L`, "there is a
measurable cardinal").  A **sentence** is a propositional combination of atoms; a
**multiverse** is a collection of worlds.  A sentence is **independent** in a
multiverse when it is true in some world and false in another — the phenomenon
witnessed for `CH` by forcing.

**Forcing** is modeled by `flip`, which toggles the truth value of an atom,
producing a "generic extension" deciding the atom the other way.  A multiverse is
**forcing-closed** when stable under all flips (an abstraction of the multiverse
axioms).  Highlights:

* `forcingClosed_atom_independent` — in a nonempty forcing-closed multiverse
  **every** atomic sentence is independent (nothing is settled by forcing);
* `CH_independent` — in the concrete two-world multiverse `{Gödel, Cohen}`, the
  Continuum Hypothesis is independent;
* `CH_independent_under_VeqL_imp_CH` — even after adopting `V = L → CH` as a law
  of the multiverse, `CH` remains independent;
* `absolute_em` / `absolute_noncontradiction` — logical validities hold across
  *all* branches, in contrast to `CH`.

Everything is proved from first principles over `Mathlib`.
-/

namespace MultiverseSetTheory

/-! ## Sentences, worlds, evaluation -/

/-- Propositional set-theoretic sentences over a type `α` of atomic assertions. -/
inductive Sentence (α : Type*) where
  | atom : α → Sentence α
  | tru : Sentence α
  | fls : Sentence α
  | neg : Sentence α → Sentence α
  | conj : Sentence α → Sentence α → Sentence α
  | disj : Sentence α → Sentence α → Sentence α
  | imp : Sentence α → Sentence α → Sentence α
  deriving DecidableEq

/-- A `World` (a model of the ambient set theory) is a truth assignment to atoms. -/
abbrev World (α : Type*) := α → Bool

/-- Boolean evaluation of a sentence in a world. -/
def eval {α} (w : World α) : Sentence α → Bool
  | .atom a => w a
  | .tru => true
  | .fls => false
  | .neg p => !(eval w p)
  | .conj p q => eval w p && eval w q
  | .disj p q => eval w p || eval w q
  | .imp p q => !(eval w p) || eval w q

/-- Satisfaction: world `w` models sentence `p`. -/
def Sat {α} (w : World α) (p : Sentence α) : Prop := eval w p = true

/-- A **multiverse** is a collection of worlds. -/
abbrev Multiverse (α : Type*) := Set (World α)

/-- `p` is **valid** across the multiverse `M` (true in every world). -/
def Valid {α} (M : Multiverse α) (p : Sentence α) : Prop := ∀ w ∈ M, Sat w p

/-- `p` is **refutable** across `M` (false in every world). -/
def Refutable {α} (M : Multiverse α) (p : Sentence α) : Prop := ∀ w ∈ M, ¬ Sat w p

/-- `p` is **independent** in `M`: true in some world and false in another. -/
def Independent {α} (M : Multiverse α) (p : Sentence α) : Prop :=
  (∃ w ∈ M, Sat w p) ∧ (∃ w ∈ M, ¬ Sat w p)

/-- `p` is **settled** in `M` if it is valid or refutable there. -/
def Settled {α} (M : Multiverse α) (p : Sentence α) : Prop :=
  Valid M p ∨ Refutable M p

/-! ## Basic satisfaction lemmas -/








/-! ## Logical validity is absolute across every multiverse -/




/-! ## Interaction of validity, refutability and independence -/






/-! ## Forcing: toggling the truth value of an atom -/

/-- The "generic extension" of a world along atom `a`: flip the truth value of `a`. -/
def flip {α} [DecidableEq α] (w : World α) (a : α) : World α :=
  fun x => if x = a then !(w x) else w x





/-- A multiverse is **forcing-closed** if it is stable under generic extensions
    (flipping any atom in any of its worlds). This abstracts the multiverse axiom
    that every universe has forcing extensions realizing the opposite of any
    forceable statement. -/
def ForcingClosed {α} [DecidableEq α] (M : Multiverse α) : Prop :=
  ∀ w ∈ M, ∀ a : α, flip w a ∈ M



/-! ## The full multiverse -/

/-- The **full multiverse**: every conceivable world. -/
def full (α : Type*) : Multiverse α := Set.univ





/-! ## Cardinality of a finite multiverse -/


/-! ## A concrete instance: CH, V = L and a measurable cardinal -/

/-- Three atomic set-theoretic assertions. -/
inductive Claim
  | CH      -- the Continuum Hypothesis
  | VeqL    -- the axiom of constructibility `V = L`
  | Meas    -- "there exists a measurable cardinal"
  deriving DecidableEq, Fintype

open Claim

/-- Gödel's constructible universe `L`: satisfies `V = L`, hence `CH`, and has no
    measurable cardinal. -/
def godel : World Claim
  | CH => true
  | VeqL => true
  | Meas => false

/-- A Cohen forcing extension in which `CH` fails (so `V = L` fails as well). -/
def cohen : World Claim
  | CH => false
  | VeqL => false
  | Meas => false

/-- The two-world multiverse `{Gödel, Cohen}`. -/
def GC : Multiverse Claim := {godel, cohen}




/-- The multiverse of worlds obeying the law `V = L → CH`. -/
def LawMV : Multiverse Claim := {w | Sat w (.imp (.atom VeqL) (.atom CH))}






end MultiverseSetTheory


