-- Prove2me | solution 1 for ExternalInterpretationDefinability.recovery_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:14.936219+00:00
-- url     : https://prove2.me/submissions/0ac39c79-6c09-477c-87c2-72fdd73560b6

-- Sol generated from Applications/ExternalInterpretationDefinability.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
/-
# The Definability Boundary for External Interpretations

An **external interpretation** of a structure `M` is a map `I : M → V` assigning
to each element of the structure a "meaning" drawn from an outside value type `V`.
The structure itself only sees its elements up to its symmetries: two elements
lying in the same orbit of the automorphism group `G` are *structurally
indistinguishable*.  The guiding question of this file is:

> When is an external interpretation *recoverable from structural truth*, i.e.
> when does it factor through the structural quotient, and when is it moreover
> *definable* in a language of invariant predicates?

The conjecture under test is:

> recoverable ⟺ constant on automorphism orbits **and** definable in the
> invariant language; for finite models orbit constancy alone suffices once the
> language is enriched by (bounded) orbit-counting modalities.

What we prove:

* **Part 1 — Orbit descent.**  `recoverable_iff_orbitConstant` : an
  interpretation factors through the orbit quotient exactly when it is constant
  on orbits, and `recovery_unique` shows the factorisation is unique.  This is
  the "necessary condition" half of the conjecture, proved in full generality.
* **Part 2 — Meaning collision.**  `not_recoverable_of_collision` and
  `perm_recoverable_iff_constant` : under the full symmetric group every
  non-constant interpretation collides, so structural truth cannot recover it;
  `meaning_collision_bool` is a concrete two-element instance.  This is the
  negative half of the classification.
* **Part 3 — Invariant languages.**  Definability in *any* invariant language
  implies orbit constancy (`definable_orbitConstant`), hence recoverability
  (`definable_recoverable`): definability is genuinely the stronger notion.
* **Part 4 — Finite sufficiency.**  For a finite model, every invariant set is
  a Boolean combination of orbit predicates (`countGen_of_invariantSet`), and
  conversely (`invariantSet_of_countGen`).  Consequently
  `finite_recoverable_iff_definable` : on finite models the three notions
  (recoverable, orbit-constant, definable in the counting language) coincide —
  the conjectured collapse in the finite case, and `orbitLang` is shown to be
  the largest invariant language (`orbitLang_maximal`).  In general (no
  finiteness) `definable_orbitLang_iff_recoverable` shows recoverability is
  exactly definability in that largest invariant language, and
  `classification_finite` packages the finite collapse as a `TFAE`.
* **Part 5 — The infinite boundary is real.**  `parity_not_definable` exhibits
  an interpretation on `ℕ` which is orbit-constant (indeed the group is trivial)
  yet undefinable in the finite/cofinite invariant language: orbit constancy
  alone is *strictly weaker* than definability, so the definability clause in
  the conjecture cannot be dropped for infinite models.
* **Part 6 — A Burnside bridge.**  `card_orbitConstant_eq_pow` counts the
  recoverable interpretations as `|V| ^ (number of orbits)`, and
  `burnside_recoverable_count` combines this with the orbit-counting lemma:
  `2 ^ (∑_g |Fix g|) = (number of recoverable Boolean interpretations) ^ |G|`,
  linking semantic recoverability to group-theoretic character sums.
-/


open ExternalInterpretationDefinability

open MulAction

universe u v w

variable {G : Type u} {M : Type v} {V : Type w} [Group G] [MulAction G M]

/-! ## Part 0 — Structural indistinguishability -/








/-! ## Part 1 — Orbit descent -/



/-! ## Part 2 — Meaning collisions: the negative half -/




/-! ## Part 3 — Invariant languages and definability -/







/-! ## Part 4 — Orbit predicates, counting modalities, and finite sufficiency -/


















/-! ## Part 5 — The infinite boundary: orbit constancy is strictly weaker -/













/-! ## Part 6 — Counting the recoverable interpretations (Burnside bridge) -/





open ExternalInterpretationDefinability in
theorem solution{I : M → V} {F₁ F₂ : orbitRel.Quotient G M → V}
    (h₁ : ∀ x : M, F₁ (Quotient.mk _ x) = I x) (h₂ : ∀ x : M, F₂ (Quotient.mk _ x) = I x) :
    F₁ = F₂ := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => rw [h₁ x, h₂ x]
