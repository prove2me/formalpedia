-- Prove2me | Theorems.Thm_ExternalInterpretationDefinability_finite_recoverable_iff_definable
-- name    : ExternalInterpretationDefinability.finite_recoverable_iff_definable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:39.665412+00:00
-- url     : https://prove2.me/theorems/cf885c1e-66a8-40f2-9a6e-4260c921edf4
-- title:
--   The finite collapse.
-- statement:
--   **The finite collapse.**  On a finite model the three notions coincide:
--   an external interpretation is recoverable from structural truth iff it is
--   constant on automorphism orbits iff each of its meaning fibres is a Boolean
--   combination of orbit-counting predicates.
--
--   ```lean
--   theorem ExternalInterpretationDefinability.finite_recoverable_iff_definable[Finite M] (I : M → V) :
--       Recoverable G I ↔ ∀ v : V, CountGen G M {x | I x = v} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ExternalInterpretationDefinability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ExternalInterpretationDefinability.lean#L309

-- Thm stub generated from Applications/ExternalInterpretationDefinability.lean
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

theorem ExternalInterpretationDefinability.finite_recoverable_iff_definable[Finite M] (I : M → V) :
    Recoverable G I ↔ ∀ v : V, CountGen G M {x | I x = v} := by sorry
