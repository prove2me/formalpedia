-- Prove2me | Definitions.Def_Applications_TangledSoundness
-- name    : Applications_TangledSoundness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:11.816351+00:00
-- url     : https://prove2.me/theorems/eb978cb7-f8e8-4d25-884e-e773db0af70c
-- title:
--   Aether Catalog definitions — Applications_TangledSoundness
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.TangledSoundness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/TangledSoundness.lean by skeleton subtraction
import Mathlib
/-
# Tangled Hierarchies: Proof Systems That Reference Their Own Soundness

A *tangled hierarchy* (Hofstadter's "strange loop") arises whenever a formal
system contains, inside itself, a predicate describing its own semantic status —
its **truth** or **soundness**.  This file constructs the order-free semantic core
of that phenomenon and proves, in a self-contained chain, that such tangles are
*unavoidable*: the moment a self-referential system can name its own soundness, a
contradiction (the Liar) is forced.

The results are built as a chain, each using the previous one:

* **`not_iff_not_self`** — the logical seed: no proposition equals its own negation.
* **`no_self_negation`, `no_liar_via_negation`** — a two-valued semantics with an
  internal negation has no Liar sentence.
* **`no_semantic_fixed_points`** — hence *full* semantic self-reference (a diagonal
  for every function) is impossible; unrestricted tangling is inconsistent.
* **`tarski_undefinability`** — Tarski's theorem: a self-referential language cannot
  contain a truth/soundness predicate satisfying the disquotation schema.  A
  companion lemma exhibits the remaining hypotheses as *satisfiable*, so the
  impossibility pins the blame precisely on the internal soundness predicate.
* **`ProofSystem`** — a system carrying external truth, internal derivability
  `Prov`, an internal provability predicate `box`, soundness, and a Gödel fixed
  point.  `exampleSystem` inhabits it, so nothing below is vacuous.
* **`godel_true_unprovable`, `godel_incompleteness`** — the Gödel sentence, which
  references its own unprovability, is *true but unprovable*; soundness is exactly
  what forces its truth.  A sound self-referential system is incomplete.
* **`soundness_predicate_not_internal`** — the capstone: in *any* proof system, an
  internal soundness predicate obeying the disquotation schema, together with the
  diagonal lemma, is contradictory.  The soundness predicate cannot consistently
  live inside the system it validates: the tangle is unavoidable.
-/


namespace TangledSoundness

/-! ## Part 0 — The logical seed -/


/-! ## Part 1 — Languages and the Liar -/

/-- A **language**: a type of sentences with a semantic truth predicate `Truth` and
an internal `neg` that acts as negation on truth values. -/
structure Language where
  /-- The sentences of the language. -/
  Sent : Type
  /-- The external (meta-level) semantics: which sentences are true. -/
  Truth : Sent → Prop
  /-- Internal negation. -/
  neg : Sent → Sent
  /-- `neg` behaves like negation on truth values. -/
  neg_truth : ∀ s, Truth (neg s) ↔ ¬ Truth s

variable (L : Language)




/-! ## Part 2 — Tarski: the soundness predicate is not internal -/



/-! ## Part 3 — A proof system with an internal provability predicate -/

/-- A **proof system**: sentences with external truth semantics, an internal
derivability predicate `Prov`, negation, an internal provability predicate `box`
(`box s` is the sentence "s is provable"), the assumption that the system is
**sound**, and a **Gödel fixed point** — a sentence asserting its own unprovability. -/
structure ProofSystem where
  /-- The sentences. -/
  Sent : Type
  /-- External semantics. -/
  Truth : Sent → Prop
  /-- Internal derivability. -/
  Prov : Sent → Prop
  /-- Internal negation. -/
  neg : Sent → Sent
  /-- Internal provability predicate: `box s` is the sentence "s is provable". -/
  box : Sent → Sent
  /-- `neg` negates truth values. -/
  neg_truth : ∀ s, Truth (neg s) ↔ ¬ Truth s
  /-- `box` correctly internalizes provability (provability *is* representable). -/
  box_truth : ∀ s, Truth (box s) ↔ Prov s
  /-- The system is sound: everything provable is true. -/
  sound : ∀ s, Prov s → Truth s
  /-- The Gödel diagonal: a sentence true exactly when it is not provable. -/
  godel : ∃ G, Truth G ↔ ¬ Prov G




/-! ## Part 4 — Capstone: the soundness predicate cannot be internal -/


end TangledSoundness


