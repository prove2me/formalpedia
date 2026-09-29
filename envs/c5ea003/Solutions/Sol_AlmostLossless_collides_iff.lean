-- Prove2me | solution 1 for AlmostLossless.collides_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:37:39.319073+00:00
-- url     : https://prove2.me/submissions/2a8afe17-eac6-4fc5-8aaa-2e36f3a87392

/-
# `AlmostLossless.collides_iff`
Target `11050396` (Open; re-read live immediately before submitting).

ORDINARY PROOF — full closure screens CLEAN (three bundles, no `Theorems.` import). Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries six):
    ∀ {α : Type} [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M} {k : Fin K} {S : Finset α} {x : α},
      AlmostLossless.Collides H k S x ↔ ∃ y ∈ S, y ≠ x ∧ H k y = H k x
**`[DecidableEq α]` but NO `[Fintype α]`**, even though section `Universal` declares
`variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}` at line 48. `collisionSet` operates on a
GIVEN `Finset S` via `.erase` and `.filter`, which need decidable equality only — never finiteness of
`α`. Lean includes what a declaration uses, so the `Fintype` is absent. Six submissions supplied it,
compiled, and were rejected on type.

DEFINITIONS (read from Def_Bridges_AlmostLosslessRandomCoding):
    collisionSet H k S x = (S.erase x).filter (fun y => H k y = H k x)
    Collides H k S x     = (collisionSet H k S x).Nonempty

MATHS. Purely a repackaging: `Finset.Nonempty` is `∃ y, y ∈ _`, `Finset.mem_filter` splits off the
hash condition, and `Finset.mem_erase` gives `y ≠ x ∧ y ∈ S`. The goal's binder `∃ y ∈ S, …` unfolds
to `∃ y, y ∈ S ∧ (y ≠ x ∧ …)`, so the two sides differ only in how the three conjuncts are nested and
ordered. Both directions are the same regrouping read in opposite order.

The content is that "collides with the codebook" — defined as a nonempty collision *set*, which is the
form the counting arguments downstream need — says exactly what it should: some OTHER codebook entry
hashes to the same bucket.
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlmostLossless

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M} {k : Fin K}
    {S : Finset α} {x : α} :
    Collides H k S x ↔ ∃ y ∈ S, y ≠ x ∧ H k y = H k x := by
  constructor
  · rintro ⟨y, hy⟩
    simp only [collisionSet, Finset.mem_filter, Finset.mem_erase] at hy
    exact ⟨y, hy.1.2, hy.1.1, hy.2⟩
  · rintro ⟨y, hyS, hyx, hH⟩
    refine ⟨y, ?_⟩
    simp only [collisionSet, Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨hyx, hyS⟩, hH⟩
