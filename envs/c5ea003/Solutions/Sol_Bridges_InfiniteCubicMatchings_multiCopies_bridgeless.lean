-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.multiCopies_bridgeless
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:46:18.224781+00:00
-- url     : https://prove2.me/submissions/c54e6473-516d-4f68-bdb2-83268770e59b

-- Sol generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
/-
# The Máčajová–Škoviera transfer: finite ⟺ infinite

`InfiniteCubicMatchingsCompactness.lean` proves that the Berge–Fulkerson and the Fan–Raspaud
conjectures transfer from finite graphs to locally finite infinite graphs admitting *finite
local models*, and `InfiniteCubicMatchingsEquivalence.lean` turns those transfers into
equivalences.  The Máčajová–Škoviera conjecture was left out, because its defining condition
quantifies over **odd cuts**, i.e. over finite vertex sets, and a local isomorphism
`φ : V → W` onto a finite model need not preserve the *cardinality* of such a set: `φ` can
collapse an odd set to an even one, destroying the parity that the conjecture is about.
(This was Conjecture 4 of `FUTURE_DIRECTIONS.md`.)

This file closes that gap.  Only one extra requirement is needed: the local model must be
*faithful* on the finite window, i.e. `φ` must be injective there.  Then the image of an odd
vertex set is again odd, and the odd-cut condition pulls back.

Main results:

* `exists_msCond_of_localIso` : pullback of a Máčajová–Škoviera pair along a local
  isomorphism, including the odd-cut half of the condition on every window on which the
  local isomorphism is injective;
* `macajovaSkoviera_of_injective_finite_local_models` : the finite Máčajová–Škoviera
  conjecture implies the infinite one on the class `HasInjectiveFiniteLocalModels`;
* `finiteMacajovaSkoviera_iff` : the two conjectures are *equivalent* on that class;
* `multiCopies` and `hasInjectiveFiniteLocalModels_multiCopies` : the class is not a
  disguised finiteness assumption — the infinite graph `multiCopies ℕ K` (infinitely many
  disjoint copies of a finite cubic bridgeless graph `K`) is cubic, bridgeless, has an
  infinite vertex set, and belongs to it.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V}

/-! ## Faithful finite local models -/





/-! ## Pullback of a Máčajová–Škoviera pair -/


/-! ## The transfer theorem and the equivalence -/




/-! ## The faithful class contains genuinely infinite graphs

A map injective on *every* finite set is injective, so a graph with infinitely many vertices
lying in `HasInjectiveFiniteLocalModels` must use larger and larger models.  Infinitely many
disjoint copies of a fixed finite cubic bridgeless graph is the simplest such example. -/









/-! ### All three properties pass unconditionally to infinite disjoint unions

Berge–Fulkerson and Fan–Raspaud transfer because the projection onto the second coordinate is
a covering map.  Máčajová–Škoviera does *not* follow from covering — the image of an odd cut
need not be odd — and is proved below by a fibre-parity argument: an odd vertex set of the
disjoint union has an odd fibre, which is an odd cut of a single copy. -/








/-! ## A concrete infinite member of the faithful class

`K₄` is finite, cubic and bridgeless, so infinitely many disjoint copies of it form an
infinite cubic bridgeless graph in `HasInjectiveFiniteLocalModels` — and all three properties
hold for it *unconditionally*. -/





open Bridges.InfiniteCubicMatchings in
theorem solution{ι : Type*} {K : SimpleGraph W} (hb : Bridgeless K) :
    Bridgeless (multiCopies ι K) := by
  rintro e he hbridge
  induction e with
  | _ p q =>
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    obtain ⟨hij, hadj⟩ : (i, a).1 = (j, b).1 ∧ K.Adj (i, a).2 (j, b).2 := he
    simp only at hij hadj
    subst hij
    rw [SimpleGraph.isBridge_iff] at hbridge
    obtain ⟨-, hreach⟩ := hbridge
    have hKreach : (K \ SimpleGraph.fromEdgeSet {s(a, b)}).Reachable a b := by
      by_contra h
      exact hb s(a, b) (by simpa using hadj) (SimpleGraph.isBridge_iff.mpr ⟨hadj, h⟩)
    refine hreach ?_
    let f : (K \ SimpleGraph.fromEdgeSet {s(a, b)}) →g
        (multiCopies ι K \ SimpleGraph.fromEdgeSet {s((i, a), (i, b))}) :=
      { toFun := fun c => (i, c)
        map_rel' := by
          rintro c d ⟨hcd, hnot⟩
          refine ⟨⟨rfl, hcd⟩, ?_⟩
          rw [SimpleGraph.fromEdgeSet_adj]
          rintro ⟨hmem, -⟩
          refine hnot ?_
          rw [SimpleGraph.fromEdgeSet_adj]
          refine ⟨?_, hcd.ne⟩
          rw [Set.mem_singleton_iff] at hmem ⊢
          rw [Sym2.eq_iff] at hmem ⊢
          rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨congrArg Prod.snd h1, congrArg Prod.snd h2⟩
          · exact Or.inr ⟨congrArg Prod.snd h1, congrArg Prod.snd h2⟩ }
    exact hKreach.map f
