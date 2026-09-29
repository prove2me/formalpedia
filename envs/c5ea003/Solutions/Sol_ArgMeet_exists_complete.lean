-- Prove2me | solution 1 for ArgMeet.exists_complete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:49:30.467534+00:00
-- url     : https://prove2.me/submissions/a3493260-decf-4ac2-a425-391f39693145

-- Sol generated from Novelty/ArgumentationMeetSemilattice.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationMeetSemilattice
import Theorems.Thm_ArgMeet_fundamental_lemma

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

theorem defends_mono {S T : Set A} (h : S ⊆ T) {a : A} (ha : Defends R S a) :
    Defends R T a := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := ha b hb
  exact ⟨c, h hc, hcb⟩




/-! ## The defense operator maps `⋂₀ 𝒮` into itself -/


/-! ## The meet of a family of complete extensions -/








/-! ## The meet is the greatest lower bound -/




/-! ## The binary meet of two complete extensions -/






/-! ## Existence of complete extensions (Zorn + Fundamental Lemma) -/


/-- The union of a chain of admissible sets is admissible. -/
theorem admissible_sUnion_chain {c : Set (Set A)} (hc : IsChain (· ⊆ ·) c)
    (hadm : ∀ S ∈ c, Admissible R S) : Admissible R (⋃₀ c) := by
  refine ⟨?_, ?_⟩
  · rintro a ⟨S1, hS1, ha⟩ b ⟨S2, hS2, hb⟩ hab
    rcases hc.total hS1 hS2 with h | h
    · exact (hadm S2 hS2).1 a (h ha) b hb hab
    · exact (hadm S1 hS1).1 a ha b (h hb) hab
  · rintro a ⟨S, hS, ha⟩
    exact defends_mono R (Set.subset_sUnion_of_mem hS) ((hadm S hS).2 a ha)


/-! ## The least complete extension (the grounded extension, order-theoretically) -/




open ArgMeet in
theorem solution: ∃ S, Complete R S := by
  obtain ⟨m, _, hmax⟩ := zorn_subset_nonempty {T | Admissible R T}
    (fun c hcsub hchain _ => ⟨⋃₀ c,
      admissible_sUnion_chain R hchain (fun S hS => hcsub hS),
      fun s hs => Set.subset_sUnion_of_mem hs⟩) ∅
    ⟨fun a ha => absurd ha (Set.notMem_empty a),
     fun a ha => absurd ha (Set.notMem_empty a)⟩
  refine ⟨m, hmax.prop, ?_⟩
  intro a ha
  have hins : Admissible R (insert a m) := fundamental_lemma R hmax.prop ha
  have heq : insert a m = m := hmax.eq_of_ge hins (Set.subset_insert a m)
  rw [← heq]; exact Set.mem_insert a m
