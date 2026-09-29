-- Prove2me | Definitions.Def_Logic_SelfQuantifyingType
-- name    : Logic_SelfQuantifyingType
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:43.722699+00:00
-- url     : https://prove2.me/theorems/ed2a7126-f533-43db-b790-6516c71bcdd2
-- title:
--   Aether Catalog definitions — Logic_SelfQuantifyingType
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.SelfQuantifyingType`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/SelfQuantifyingType.lean by skeleton subtraction
import Mathlib

/-!
# Self-Quantifying Types and the Diagonal Core of Self-Reference

A *self-quantifying type* is a type `T` that can name every predicate about
itself: informally `T ≈ Π (x : T), P x`, equivalently `T ≃ (T → Prop)`.  Such a
type would be able to reflect on all of its own properties from within.  This
module proves, from a single structural root — Lawvere's fixed-point theorem —
that no such type exists, and then follows the same diagonal argument through its
classical incarnations in cardinal arithmetic (Cantor), the undefinability of
truth (Tarski) and incompleteness (Gödel).

## Main results

* `lawvere_fixed_point` — the structural heart of every diagonal argument: a
  point-surjective family `A → (A → B)` forces *every* self-map of `B` to have a
  fixed point.
* `no_selfquant_surjection` — no type surjects onto its own predicate space
  `T → (T → Prop)` (Cantor, obtained from Lawvere via the fixed-point-free map
  `Not` on `Prop`).
* `no_selfquant_injection` — dually, the predicate space never injects back into
  the type.
* `isEmpty_selfquant_equiv` — the self-quantifying equivalence `T ≃ (T → Prop)`
  is impossible.
* `selfquant_cardinal_strict` — the quantitative shadow: `#T < #(T → Prop)`,
  bridging the logical obstruction with cardinal arithmetic.
* `SelfRefSystem.goedel_true` / `goedel_unprovable` — a system whose provability
  predicate is internally nameable contains a true but unprovable sentence.
* `SelfRefSystem.tarski_truth_not_definable` — in the same system truth itself is
  *not* internally nameable: the exact boundary that keeps Gödel's argument
  consistent while Tarski's collapses.

## References

* Lawvere, F.W. *Diagonal arguments and cartesian closed categories* (1969).
* Yanofsky, N. *A universal approach to self-referential paradoxes* (2003).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): a "fully self-quantifying" type `T ≃ (T → Prop)`
cannot exist, and the obstruction is one and the same as Cantor's, Tarski's and
Gödel's. Conjecture: all four follow from Lawvere's fixed-point theorem plus the
single fact that `Not : Prop → Prop` has no fixed point.

Experiment (Experimenter): proved `lawvere_fixed_point` by the diagonal map
`d a = g (f a a)`; instantiating `B := Prop`, `g := Not` yields Cantor
immediately. Cardinality was recovered from `Cardinal.cantor`. For Tarski/Gödel
the naive structure with an *unrestricted* diagonal on the truth predicate is
inconsistent (derives `False`), which is exactly Tarski's theorem — so the
diagonal had to be *restricted to internally definable predicates*.

Analysis (Analyst): the key structural pattern is that Gödel and Tarski differ
only in *which* predicates a system can name. If negated provability is nameable
one gets a true-but-unprovable sentence (Gödel); if negated truth were nameable
one would get an outright contradiction — hence truth is not nameable (Tarski).
Both live on the same `diag_spec` fixed point, only the `Definable` gate differs.

Critique (Critic): to rule out vacuity of the `SelfRefSystem` hypotheses we
exhibit `exampleSystem`, a concrete satisfying model, so the Gödel/Tarski
theorems are not vacuously true. Every main theorem uses an insight-bearing
tactic (`obtain`, `by_contra`/`intro`, `tauto`, `simpa`) rather than `decide`.

Synthesis (PI): one lemma — Lawvere — organises the whole family; the
`Definable` gate is the precise dial separating consistency from paradox.
-- !-- Lab Notes -- !--
-/

open Function

namespace SelfQuantifying

/-! ## Part 1 — Lawvere's fixed-point theorem, the structural root -/



/-! ## Part 2 — The self-quantifying type cannot exist -/





/-! ## Part 3 — The quantitative shadow: a strict cardinal gap -/


/-! ## Part 4 — Truth, provability and the definability boundary

We now formalise a self-referential system.  Its diagonal operator produces,
for every *internally definable* predicate `φ`, a sentence whose truth value is
`φ` applied to itself.  Restricting the diagonal to definable predicates is
exactly what keeps the system consistent: Gödel's sentence exists because
negated provability is definable, while Tarski's paradox is blocked because
negated truth is proven *not* definable. -/

/-- A `SelfRefSystem` carries sentences with a truth predicate `Tr`, a
provability predicate `Pr` (sound: provable implies true), a notion of which
predicates are internally `Definable`, and a diagonal operator satisfying the
fixed-point property on definable predicates.  We further assume that negated
provability is definable — the standard representability hypothesis. -/
structure SelfRefSystem where
  /-- The type of sentences. -/
  Sentence : Type
  /-- Truth of a sentence (a metatheoretic proposition). -/
  Tr : Sentence → Prop
  /-- Provability of a sentence. -/
  Pr : Sentence → Prop
  /-- Soundness: provable sentences are true. -/
  sound : ∀ s, Pr s → Tr s
  /-- Which predicates over sentences are internally nameable. -/
  Definable : (Sentence → Prop) → Prop
  /-- The diagonal (self-reference) operator. -/
  diag : (Sentence → Prop) → Sentence
  /-- Diagonal fixed-point property, available for definable predicates. -/
  diag_spec : ∀ φ : Sentence → Prop, Definable φ → (Tr (diag φ) ↔ φ (diag φ))
  /-- Negated provability is internally definable (representability). -/
  negPr_definable : Definable (fun s => ¬ Pr s)

namespace SelfRefSystem

variable (M : SelfRefSystem)

/-- The Gödel sentence: the diagonal fixed point of "is not provable". -/
def goedel : M.Sentence := M.diag (fun s => ¬ M.Pr s)





end SelfRefSystem


end SelfQuantifying


