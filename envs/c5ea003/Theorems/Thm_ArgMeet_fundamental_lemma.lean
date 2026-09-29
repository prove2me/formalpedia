-- Prove2me | Theorems.Thm_ArgMeet_fundamental_lemma
-- name    : ArgMeet.fundamental_lemma
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:55.909364+00:00
-- url     : https://prove2.me/theorems/e71c7216-5d85-4779-a4db-e7055e91220f
-- title:
--   Dung's Fundamental Lemma.
-- statement:
--   **Dung's Fundamental Lemma.**  If `S` is admissible and defends `a`, then
--   `insert a S` is again admissible.
--
--   ```lean
--   theorem ArgMeet.fundamental_lemma{S : Set A} (hS : Admissible R S) {a : A}
--       (ha : Defends R S a) : Admissible R (insert a S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ArgumentationMeetSemilattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ArgumentationMeetSemilattice.lean#L246

-- Thm stub generated from Novelty/ArgumentationMeetSemilattice.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationMeetSemilattice

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

open ArgMeet

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/







/-! ## Monotonicity and elementary facts -/





/-! ## The defense operator maps `⋂₀ 𝒮` into itself -/


/-! ## The meet of a family of complete extensions -/








/-! ## The meet is the greatest lower bound -/




/-! ## The binary meet of two complete extensions -/






/-! ## Existence of complete extensions (Zorn + Fundamental Lemma) -/

theorem ArgMeet.fundamental_lemma{S : Set A} (hS : Admissible R S) {a : A}
    (ha : Defends R S a) : Admissible R (insert a S) := by sorry
