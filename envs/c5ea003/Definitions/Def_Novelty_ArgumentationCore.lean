-- Prove2me | Definitions.Def_Novelty_ArgumentationCore
-- name    : Novelty_ArgumentationCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:51.697952+00:00
-- url     : https://prove2.me/theorems/253df408-0cf5-4a97-9b26-145b41ca6ec3
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationCore.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, I: Dung semantics and the defense operator

An *argumentation framework* (AF) in the sense of Dung is a pair `(A, R)` where
`A` is a set of *arguments* and `R : A → A → Prop` is an *attack relation*
(`R a b` reads "argument `a` attacks argument `b`").  We model an AF by a fixed
relation `R` on an arbitrary type `A`.

This file develops the classical acceptability semantics entirely from scratch:

* `ConflictFree S` — no argument of `S` attacks another argument of `S`.
* `Defends S a`   — every attacker of `a` is counter-attacked by some member of `S`.
* `charF S`       — the *characteristic (defense) operator*, `{a | S defends a}`.
* `Admissible S`  — `S` is conflict-free and defends each of its members.

The main results are:

* `admissible_iff`      — `S` is admissible iff conflict-free and `S ⊆ charF S`.
* `charF_mono`          — the defense operator is monotone.
* `conflictFree_charF`  — the defense operator *preserves* conflict-freeness.
* `conflictFree_subset` — conflict-free sets are downward closed (this is what
  makes the conflict-free sets a *simplicial complex*, developed in
  `ArgumentationSimplicial`).
* `fundamental_lemma`   — **Dung's Fundamental Lemma**: if `S` is admissible and
  defends `a`, then `insert a S` is again admissible.

These are the load-bearing lemmas for the theory of preferred and grounded
extensions in `ArgumentationExtensions`.
-/

namespace ArgTop

variable {A : Type*} (R : A → A → Prop)

/-- `S` is *conflict-free*: no argument in `S` attacks another argument in `S`. -/
def ConflictFree (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` *defends* `a`: every attacker `b` of `a` is itself attacked by some
member `c` of `S`. -/
def Defends (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is *admissible*: it is conflict-free and defends each of its members. -/
def Admissible (S : Set A) : Prop := ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The *characteristic operator* (Dung's `F`): `charF S` is the set of all
arguments defended by `S`. -/
def charF (S : Set A) : Set A := {a | Defends R S a}



/-- Defense is monotone in the defending set. -/
theorem defends_mono {S T : Set A} (h : S ⊆ T) {a : A} (ha : Defends R S a) :
    Defends R T a := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := ha b hb
  exact ⟨c, h hc, hcb⟩

/-- The characteristic operator is monotone: larger sets defend more arguments. -/
theorem charF_mono {S T : Set A} (h : S ⊆ T) : charF R S ⊆ charF R T :=
  fun _ ha => defends_mono R h ha



/-- **Conflict-free sets are downward closed.**  A subset of a conflict-free set
is conflict-free.  This is exactly the axiom that makes the family of
conflict-free sets an abstract simplicial complex on the vertex set `A`. -/
theorem conflictFree_subset {S T : Set A} (h : S ⊆ T) (hT : ConflictFree R T) :
    ConflictFree R S :=
  fun a ha b hb => hT a (h ha) b (h hb)





end ArgTop


