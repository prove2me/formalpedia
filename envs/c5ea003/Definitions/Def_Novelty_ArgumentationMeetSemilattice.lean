-- Prove2me | Definitions.Def_Novelty_ArgumentationMeetSemilattice
-- name    : Novelty_ArgumentationMeetSemilattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:57.377776+00:00
-- url     : https://prove2.me/theorems/58c07930-3cb0-4bef-8a29-4d04d09d9a47
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationMeetSemilattice
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationMeetSemilattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationMeetSemilattice.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, IX: the complete extensions form a meet-semilattice

This file is **self-contained** (it re-declares the basic Dung semantics from
`ArgumentationCore` / `ArgumentationExtensions`) and settles **Conjecture 1** of
the *Future Directions* cycle:

> Every nonempty family of complete extensions has a greatest lower bound that is
> again complete, and this bound is computed by iterating the defense operator
> from the intersection.

Recall from the earlier development that an argumentation framework is a relation
`R : A → A → Prop`, with defense operator `charF`, and that a set `S` is
*complete* when it is conflict-free and a fixed point of `charF`.  A complete
extension is exactly a conflict-free fixed point of the (monotone) defense
operator.

## The construction

Given a family `𝒮` of complete extensions, put `I := ⋂₀ 𝒮`.  The decisive
observation is that

  `charF I ⊆ I`   (`charF_sInter_subset`)

because `I ⊆ E` for each `E ∈ 𝒮`, monotonicity gives `charF I ⊆ charF E = E`,
and intersecting over `E` yields `charF I ⊆ I`.  Thus `charF` restricts to a
monotone self-map of the interval `[⊥, I]`, and its **greatest fixed point there**
— the largest conflict-free fixed point below `I` — is the desired meet.  We build
that greatest post-fixed point by hand (a Knaster–Tarski union):

  `familyMeet 𝒮 := ⋃₀ {S | S ⊆ I ∧ S ⊆ charF S}`.

## The chain of results

* `complete_charF_eq`        — a complete extension is a fixed point of `charF`;
* `charF_sInter_subset`      — `charF` maps the intersection of complete
  extensions into itself;
* `familyMeet_subset_sInter` — the meet lies below the intersection;
* `familyMeet_postfixed`     — the meet is a post-fixed point of `charF`;
* `familyMeet_fixed`         — the meet is a **fixed point** of `charF`;
* `familyMeet_conflictFree`  — the meet is conflict-free;
* `familyMeet_complete`      — **the meet is a complete extension**;
* `familyMeet_subset_of_mem` / `le_familyMeet` — it is a lower bound, and the
  *greatest* lower bound, among complete extensions;
* `familyMeet_isGLB`         — **the complete extensions form a meet-semilattice**:
  every nonempty family has a complete greatest lower bound;
* `completeInf` / `completeInf_complete` / `completeInf_isGLB` — the binary meet
  of two complete extensions.

## The order-theoretic derivation of the grounded extension

Feeding the family of *all* complete extensions into the meet reconstructs the
**least complete extension** — the grounded extension — purely order-theoretically,
sidestepping the transfinite fixed-point induction of `ArgumentationGrounded`:

* `exists_complete`        — a complete extension exists (Zorn + Fundamental Lemma);
* `exists_least_complete`  — **there is a least complete extension**, namely the
  meet of the family of all complete extensions;
* `least_complete_unique`  — it is unique (the grounded extension, characterized
  order-theoretically as the bottom of the meet-semilattice).
-/

namespace ArgMeet

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/

/-- `S` is *conflict-free*: no argument in `S` attacks another in `S`. -/
def ConflictFree (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` *defends* `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is *admissible*: conflict-free and defends all its members. -/
def Admissible (S : Set A) : Prop := ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The *characteristic (defense) operator*: `charF S` is the set of arguments
defended by `S`. -/
def charF (S : Set A) : Set A := {a | Defends R S a}

/-- `S` is a **complete extension**: admissible and closed under defense. -/
def Complete (S : Set A) : Prop := Admissible R S ∧ charF R S ⊆ S


/-! ## Monotonicity and elementary facts -/





/-! ## The defense operator maps `⋂₀ 𝒮` into itself -/


/-! ## The meet of a family of complete extensions -/

/-- **The meet** of a family `𝒮`: the union of all post-fixed points of `charF`
contained in the intersection `⋂₀ 𝒮`.  This is the greatest fixed point of the
defense operator below the intersection. -/
def familyMeet (𝒮 : Set (Set A)) : Set A :=
  ⋃₀ {S | S ⊆ ⋂₀ 𝒮 ∧ S ⊆ charF R S}







/-! ## The meet is the greatest lower bound -/




/-! ## The binary meet of two complete extensions -/

/-- The **binary meet** of two complete extensions. -/
def completeInf (S T : Set A) : Set A := familyMeet R ({S, T} : Set (Set A))





/-! ## Existence of complete extensions (Zorn + Fundamental Lemma) -/




/-! ## The least complete extension (the grounded extension, order-theoretically) -/



end ArgMeet


